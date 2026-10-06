module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Constructions

@[expose] public section

namespace DifferentialGeometry.Topology

universe u v w

abbrev ClosedCell (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ ≤ 1}

abbrev CellBoundary (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ = 1}

abbrev CellInterior (n : ℕ) : Type :=
  {x : EuclideanSpace ℝ (Fin n) // ‖x‖ < 1}

def cellBoundaryInclusion (n : ℕ) : CellBoundary n → ClosedCell n :=
  fun x => ⟨x, le_of_eq x.2⟩

def closedCellCenter (n : ℕ) : ClosedCell n :=
  ⟨0, by simp⟩

def cellInteriorInclusion (n : ℕ) : CellInterior n → ClosedCell n :=
  fun x => ⟨x, le_of_lt x.2⟩

def adjunctionRel {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    B ⊕ X → B ⊕ X → Prop :=
  fun a b =>
    ∃ x : A,
      (a = Sum.inl (i x) ∧ b = Sum.inr (φ x)) ∨
        (b = Sum.inl (i x) ∧ a = Sum.inr (φ x))

abbrev AdjunctionSpace {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    Type (max w u) :=
  Quot (adjunctionRel i φ)

def adjunctionMk {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    B ⊕ X → AdjunctionSpace i φ :=
  Quot.mk (adjunctionRel i φ)

def adjunctionLower {A : Type v} {B : Type w} {X : Type u} {i : A → B} (φ : A → X) :
    X → AdjunctionSpace i φ :=
  fun x => adjunctionMk i φ (Sum.inr x)

def adjunctionCell {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X) :
    B → AdjunctionSpace i φ :=
  fun d => adjunctionMk i φ (Sum.inl d)

theorem adjunction_coherence {A : Type v} {B : Type w} {X : Type u} (i : A → B) (φ : A → X)
    (x : A) :
    adjunctionCell i φ (i x) = adjunctionLower φ (φ x) :=
  Quot.sound ⟨x, Or.inl ⟨rfl, rfl⟩⟩

abbrev CellAdjunctionSpace {X : Type u} (n : ℕ) (φ : CellBoundary n → X) : Type u :=
  AdjunctionSpace (cellBoundaryInclusion n) φ

end DifferentialGeometry.Topology
