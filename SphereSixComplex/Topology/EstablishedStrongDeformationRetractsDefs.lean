module

public import Mathlib.Topology.Homotopy.Equiv

/-!
# Subspace inclusions and homotopy-equivalent subspace inclusions

This module carries the two source-independent definitions through which the rest of the library
speaks about a subspace inclusion: the inclusion map itself and the predicate saying that it is a
homotopy equivalence with the literal inclusion recorded as the inverse.

Only these definitions live here.  The strong-deformation-retract principles built on them are in
`EstablishedStrongDeformationRetracts`, which is downstream of
`ContractibleRegularCoverInclusionProof`; that proof file needs the two definitions below, so they
are split out to keep the import graph acyclic.
-/

@[expose] public section

noncomputable section

open scoped ContinuousMap

namespace SphereSixComplex

/-- The continuous inclusion of a subspace. -/
public def topologicalSubsetInclusionMap {X : Type*} [TopologicalSpace X] (A : Set X) :
    C(A, X) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

/-- The inclusion `A ⊆ X` is a homotopy equivalence, with its inverse map recorded explicitly. -/
public def IsHomotopyEquivalenceInclusion {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ e : X ≃ₕ A, e.invFun = topologicalSubsetInclusionMap A

end SphereSixComplex

end

end
