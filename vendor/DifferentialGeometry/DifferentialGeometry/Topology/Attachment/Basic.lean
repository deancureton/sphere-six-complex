module

public import DifferentialGeometry.Topology.Attachment.Defs
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Defs.Induced
public import Mathlib.Topology.Maps.Basic

@[expose] public section

namespace DifferentialGeometry.Topology

universe u v w t

open Filter Function Set

instance (n : ℕ) : CompactSpace (ClosedCell n) := by
  have h : IsCompact ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1} : Set (EuclideanSpace ℝ (Fin n))) := by
    have heq : ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ ≤ 1} : Set _) =
        Metric.closedBall 0 1 := by
      ext x
      simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    rw [heq]
    exact isCompact_closedBall (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)
  exact isCompact_iff_compactSpace.mp h

instance (n : ℕ) : CompactSpace (CellBoundary n) := by
  have h : IsCompact ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ = 1} : Set (EuclideanSpace ℝ (Fin n))) := by
    have heq : ({x : EuclideanSpace ℝ (Fin n) | ‖x‖ = 1} : Set _) =
        Metric.sphere 0 1 := by
      ext x
      simp only [Set.mem_ofPred_eq, Metric.mem_sphere, dist_zero_right]
    rw [heq]
    exact isCompact_sphere (x := (0 : EuclideanSpace ℝ (Fin n))) (r := 1)
  exact isCompact_iff_compactSpace.mp h

theorem continuous_cellBoundaryInclusion (n : ℕ) : Continuous (cellBoundaryInclusion n) := by
  exact continuous_subtype_val.subtype_mk (p := fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ≤ 1)
    (fun x : CellBoundary n => le_of_eq x.2)

theorem injective_cellBoundaryInclusion (n : ℕ) : Function.Injective (cellBoundaryInclusion n) := by
  intro x y h
  have hval : (x : EuclideanSpace ℝ (Fin n)) = (y : EuclideanSpace ℝ (Fin n)) := by
    simpa [cellBoundaryInclusion] using
      congrArg (fun z : ClosedCell n => (z : EuclideanSpace ℝ (Fin n))) h
  apply Subtype.ext
  exact hval

theorem range_closedCell (n : ℕ) :
    Set.range (fun x : ClosedCell n => (x : EuclideanSpace ℝ (Fin n))) =
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [Metric.closedBall]
  · intro hx
    exact ⟨⟨x, by simpa [Metric.closedBall] using hx⟩, rfl⟩

theorem range_cellBoundary (n : ℕ) :
    Set.range (fun x : CellBoundary n => (x : EuclideanSpace ℝ (Fin n))) =
      Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    simp [Metric.sphere]
  · intro hx
    exact ⟨⟨x, by simpa [Metric.sphere] using hx⟩, rfl⟩

section AdjunctionSpace

variable {A : Type v} {B : Type w} [TopologicalSpace B] {X : Type u} [TopologicalSpace X]

theorem continuous_adjunctionMk (i : A → B) (φ : A → X) : Continuous (adjunctionMk i φ) :=
  continuous_quot_mk

theorem continuous_adjunctionLower (i : A → B) (φ : A → X) :
    Continuous (adjunctionLower (i := i) φ) :=
  continuous_quot_mk.comp continuous_inr

theorem continuous_adjunctionCell (i : A → B) (φ : A → X) : Continuous (adjunctionCell i φ) :=
  continuous_quot_mk.comp continuous_inl

theorem isQuotientMap_adjunctionMk (i : A → B) (φ : A → X) :
    Topology.IsQuotientMap (adjunctionMk i φ) :=
  isQuotientMap_quot_mk

theorem continuous_adjunction_lift (i : A → B) (φ : A → X) {Y : Type t} [TopologicalSpace Y]
    {f : B ⊕ X → Y}
    (hr : ∀ a b : B ⊕ X, adjunctionRel i φ a b → f a = f b) (hf : Continuous f) :
    Continuous (Quot.lift f hr : AdjunctionSpace i φ → Y) :=
  continuous_quot_lift hr hf

theorem adjunction_cell_eq_lower_iff {A : Type v} {B : Type w} {X : Type u}
    (i : A → B) (φ : A → X) (hφ : Function.Injective φ) (b : B) (x : X) :
    adjunctionCell i φ b = adjunctionLower φ x ↔ ∃ a, i a = b ∧ φ a = x := by
  have key : ∀ a : A, (i a = b) = (∃ a', i a' = b ∧ φ a' = φ a) := by
    intro a
    apply propext
    constructor
    · intro h
      exact ⟨a, h, rfl⟩
    · rintro ⟨a', ha', hφ'⟩
      exact ((congrArg i (hφ hφ')).symm).trans ha'
  constructor
  · intro h
    let f : B ⊕ X → Prop := Sum.elim (fun b' => b' = b)
      (fun x' => ∃ a, i a = b ∧ φ a = x')
    have hf : ∀ u v, adjunctionRel i φ u v → f u = f v := by
      rintro u v ⟨a, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact key a
      · exact (key a).symm
    let g : AdjunctionSpace i φ → Prop := Quot.lift f hf
    have hh := congrArg g h
    change f (Sum.inl b) = f (Sum.inr x) at hh
    change (b = b) = (∃ a, i a = b ∧ φ a = x) at hh
    exact Eq.mp hh rfl
  · rintro ⟨a, rfl, rfl⟩
    exact adjunction_coherence i φ a

theorem connectedSpace_adjunctionSpace {A : Type*} {B : Type*} {X : Type*}
    [TopologicalSpace B] [TopologicalSpace X] [ConnectedSpace B] [ConnectedSpace X] [Nonempty A]
    (i : A → B) (φ : A → X) : ConnectedSpace (AdjunctionSpace i φ) := by
  have hcov : Set.range (adjunctionCell i φ) ∪ Set.range (adjunctionLower (i := i) φ) = univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    exact Quot.induction_on q fun s => by
      cases s with
      | inl b => exact Or.inl ⟨b, rfl⟩
      | inr x => exact Or.inr ⟨x, rfl⟩
  obtain ⟨z⟩ := ‹Nonempty A›
  have hne : (Set.range (adjunctionCell i φ) ∩
      Set.range (adjunctionLower (i := i) φ)).Nonempty :=
    ⟨adjunctionCell i φ (i z),
      ⟨⟨i z, rfl⟩, ⟨φ z, (adjunction_coherence i φ z).symm⟩⟩⟩
  rw [connectedSpace_iff_univ, ← hcov]
  exact IsConnected.union hne (isConnected_range (continuous_adjunctionCell i φ))
    (isConnected_range (continuous_adjunctionLower i φ))

theorem pathConnectedSpace_adjunctionSpace {A : Type*} {B : Type*} {X : Type*}
    [TopologicalSpace B] [TopologicalSpace X] [PathConnectedSpace B] [PathConnectedSpace X]
    [Nonempty A] (i : A → B) (φ : A → X) : PathConnectedSpace (AdjunctionSpace i φ) := by
  have hcov : Set.range (adjunctionCell i φ) ∪ Set.range (adjunctionLower (i := i) φ) = univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    exact Quot.induction_on q fun s => by
      cases s with
      | inl b => exact Or.inl ⟨b, rfl⟩
      | inr x => exact Or.inr ⟨x, rfl⟩
  obtain ⟨z⟩ := ‹Nonempty A›
  have hne : (Set.range (adjunctionCell i φ) ∩
      Set.range (adjunctionLower (i := i) φ)).Nonempty :=
    ⟨adjunctionCell i φ (i z),
      ⟨⟨i z, rfl⟩, ⟨φ z, (adjunction_coherence i φ z).symm⟩⟩⟩
  rw [pathConnectedSpace_iff_univ, ← hcov]
  exact IsPathConnected.union (isPathConnected_range (continuous_adjunctionCell i φ))
    (isPathConnected_range (continuous_adjunctionLower i φ)) hne

end AdjunctionSpace

end DifferentialGeometry.Topology
