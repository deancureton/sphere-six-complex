module

public import SphereSixComplex.Topology.WangHomologyPresentation

/-!
# Sign ambiguity of exact Wang presentations

Exactness alone does not orient a connecting homomorphism.  Negating the boundary of a
`WangHomologyPresentation` preserves all three exactness assertions.  Consequently, a comparison
with a chain-level Mayer--Vietoris boundary requires an oriented chain model of the Wang sequence,
not merely the exact presentation currently exposed by the general mapping-torus theorem.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]

/-- Negating the connecting homomorphism preserves a Wang presentation. -/
public noncomputable def negBoundary
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low) :
    WangHomologyPresentation HighRelations High Total LowRelations Low where
  highDifference := P.highDifference
  inclusion := P.inclusion
  boundary := -P.boundary
  lowDifference := P.lowDifference
  exact_highDifference_inclusion := P.exact_highDifference_inclusion
  exact_inclusion_boundary := by
    intro y
    constructor
    · intro hy
      apply (P.exact_inclusion_boundary y).mp
      simpa using hy
    · intro hy
      have h := (P.exact_inclusion_boundary y).mpr hy
      simpa using h
  exact_boundary_lowDifference := by
    intro y
    constructor
    · intro hy
      obtain ⟨x, hx⟩ := (P.exact_boundary_lowDifference y).mp hy
      exact ⟨-x, by simp [hx]⟩
    · rintro ⟨x, hx⟩
      apply (P.exact_boundary_lowDifference y).mpr
      exact ⟨-x, by simpa using hx⟩

@[simp]
public theorem negBoundary_boundary
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low) :
    P.negBoundary.boundary = -P.boundary :=
  rfl

end SphereSixComplex.WangHomologyPresentation
