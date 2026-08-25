module

public import SphereSixComplex.Topology.BoundarySevenCechGlobalComparison
public import SphereSixComplex.Topology.BoundarySevenFaceNeighborhoodIntersectionHomology

/-!
# Ordered tuples for the boundary-seven Cech nerves

This file contains only the common finite indexing data used by the independent source- and
target-side objectwise decompositions of the two Cech nerves.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits Simplicial

namespace SphereSixComplex

/-- An ordered choice of one of the eight facets in every slot of an outer Cech degree. -/
public abbrev BoundarySevenCechTuple (n : SimplexCategoryᵒᵖ) :=
  Fin (n.unop.len + 1) → Fin 8

namespace BoundarySevenCechTuple

/-- The unordered support of an ordered Cech tuple. -/
public def support {n : SimplexCategoryᵒᵖ} (a : BoundarySevenCechTuple n) :
    Finset (Fin 8) :=
  Finset.univ.image a

@[simp]
public theorem mem_support {n : SimplexCategoryᵒᵖ} (a : BoundarySevenCechTuple n)
    (i : Fin (n.unop.len + 1)) :
    a i ∈ a.support :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

public theorem support_nonempty {n : SimplexCategoryᵒᵖ} (a : BoundarySevenCechTuple n) :
    a.support.Nonempty :=
  ⟨a 0, a.mem_support 0⟩

end BoundarySevenCechTuple

/-- Tuples with proper support.  The omitted full-support tuples correspond on both sides to
the empty eightfold intersection. -/
public abbrev BoundarySevenProperCechTuple (n : SimplexCategoryᵒᵖ) :=
  {a : BoundarySevenCechTuple n // a.support ≠ Finset.univ}

namespace BoundarySevenProperCechTuple

public theorem support_nonempty {n : SimplexCategoryᵒᵖ}
    (a : BoundarySevenProperCechTuple n) :
    a.1.support.Nonempty :=
  a.1.support_nonempty

public theorem support_ssubset_univ {n : SimplexCategoryᵒᵖ}
    (a : BoundarySevenProperCechTuple n) :
    a.1.support ⊂ Finset.univ :=
  Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, a.2⟩

public theorem support_compl_nonempty {n : SimplexCategoryᵒᵖ}
    (a : BoundarySevenProperCechTuple n) :
    a.1.supportᶜ.Nonempty := by
  apply Finset.nonempty_of_ne_empty
  intro h
  exact a.2 ((Finset.compl_eq_empty_iff _).mp h)

end BoundarySevenProperCechTuple

end SphereSixComplex
