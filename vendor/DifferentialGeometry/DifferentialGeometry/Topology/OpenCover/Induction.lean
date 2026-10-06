module

public import Mathlib.Topology.Bases
public import Mathlib.Data.Set.Finite.Lattice

@[expose] public section

open Set

namespace TopologicalSpace.IsTopologicalBasis

universe u

variable {X : Type u} [TopologicalSpace X] {B : Set (Set X)} {P : Set X → Prop}

private theorem finite_union_inter_property (hB : IsTopologicalBasis B)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B ∨ U ∩ V = ∅)
    (hzero : P ∅) (hbasis : ∀ U ∈ B, P U)
    (hunion : ∀ U V : Set X, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) → P (U ∪ V))
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, U i ∈ B) (F : Finset ι) :
    P (⋃ i ∈ F, U i) ∧ ∀ V ∈ B, P ((⋃ i ∈ F, U i) ∩ V) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using And.intro hzero (fun V (_ : V ∈ B) => hzero)
  | @insert i F hi ih =>
    have hopen : IsOpen (⋃ j ∈ F, U j) := isOpen_iUnion fun j => isOpen_iUnion fun _ => hB.isOpen (hU j)
    have heq : (⋃ j ∈ insert i F, U j) = U i ∪ ⋃ j ∈ F, U j := by simp
    rw [heq]
    constructor
    · apply hunion _ _ (hB.isOpen (hU i)) hopen (hbasis _ (hU i)) ih.1
      simpa only [inter_comm] using ih.2 (U i) (hU i)
    · intro V hV
      rw [union_inter_distrib_right]
      have hiV : P (U i ∩ V) := by
        rcases hinter (U i) (hU i) V hV with h | h
        · exact hbasis _ h
        · exact h ▸ hzero
      apply hunion _ _ ((hB.isOpen (hU i)).inter (hB.isOpen hV))
        (hopen.inter (hB.isOpen hV)) hiV (ih.2 V hV)
      have heq : (U i ∩ V) ∩ ((⋃ j ∈ F, U j) ∩ V) = (⋃ j ∈ F, U j) ∩ (U i ∩ V) := by
        ext x
        simp only [mem_inter_iff]
        tauto
      rw [heq]
      rcases hinter (U i) (hU i) V hV with h | h
      · exact ih.2 (U i ∩ V) h
      · simpa only [h, inter_empty] using hzero

theorem isOpen_induction_of_union_of_directed_sUnion (hB : IsTopologicalBasis B)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ∩ V ∈ B ∨ U ∩ V = ∅)
    (hzero : P ∅) (hbasis : ∀ U ∈ B, P U)
    (hunion : ∀ U V : Set X, IsOpen U → IsOpen V → P U → P V → P (U ∩ V) → P (U ∪ V))
    (hdirected : ∀ S : Set (Set X), S.Nonempty → DirectedOn (· ⊆ ·) S →
      (∀ U ∈ S, IsOpen U ∧ P U) → P (⋃₀ S))
    {W : Set X} (hW : IsOpen W) : P W := by
  classical
  let I := {U : Set X // U ∈ B ∧ U ⊆ W}
  let unionOf (F : Finset I) : Set X := ⋃ i ∈ F, i.val
  let S : Set (Set X) := range unionOf
  have hSnonempty : S.Nonempty := ⟨unionOf ∅, ∅, rfl⟩
  have hSdirected : DirectedOn (· ⊆ ·) S := by
    rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
    refine ⟨unionOf (F ∪ G), ⟨F ∪ G, rfl⟩, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_union_left G hi, hx⟩
    · intro x hx
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_union_right F hi, hx⟩
  have hS : ∀ U ∈ S, IsOpen U ∧ P U := by
    rintro _ ⟨F, rfl⟩
    exact ⟨isOpen_iUnion fun i => isOpen_iUnion fun _ => hB.isOpen i.property.1,
      (finite_union_inter_property hB hinter hzero hbasis hunion
        (fun i : I => i.val) (fun i => i.property.1) F).1⟩
  have heq : ⋃₀ S = W := by
    ext x
    constructor
    · rintro ⟨_, ⟨F, rfl⟩, hx⟩
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
      exact i.property.2 hx
    · intro hx
      obtain ⟨U, hUB, hxU, hUW⟩ := hB.exists_subset_of_mem_open hx hW
      let i : I := ⟨U, hUB, hUW⟩
      refine ⟨unionOf {i}, ⟨{i}, rfl⟩, ?_⟩
      exact mem_iUnion₂.mpr ⟨i, Finset.mem_singleton_self i, hxU⟩
  rw [← heq]
  exact hdirected S hSnonempty hSdirected hS

end TopologicalSpace.IsTopologicalBasis
