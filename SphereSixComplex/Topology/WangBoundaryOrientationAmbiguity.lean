module

public import SphereSixComplex.Topology.WangBoundarySignAmbiguity

/-!
# Orientation ambiguity of an abstract Wang presentation

Exactness alone does not orient a connecting homomorphism: negating the boundary preserves all
three exactness conditions.  Consequently, comparison with a geometric Mayer--Vietoris boundary
requires either a chain-level realization of the Wang sequence or a separately oriented
geometric comparison.
-/

@[expose] public section

noncomputable section

namespace SphereSixComplex.WangHomologyPresentation

variable {HighRelations High Total LowRelations Low : Type*}
  [AddCommGroup HighRelations] [AddCommGroup High] [AddCommGroup Total]
  [AddCommGroup LowRelations] [AddCommGroup Low]

/-- If a boundary value is not fixed by negation, exactness admits two distinct choices of its
orientation. -/
public theorem negBoundary_boundary_ne_of_apply_ne_neg
    (P : WangHomologyPresentation HighRelations High Total LowRelations Low)
    {x : Total} (hx : -P.boundary x ≠ P.boundary x) :
    P.negBoundary.boundary ≠ P.boundary := by
  intro h
  have hx' := DFunLike.congr_fun h x
  simp only [negBoundary_boundary, AddMonoidHom.neg_apply] at hx'
  exact hx hx'

end SphereSixComplex.WangHomologyPresentation
