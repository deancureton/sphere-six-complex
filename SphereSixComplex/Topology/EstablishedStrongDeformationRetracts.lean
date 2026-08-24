module

public import SphereSixComplex.Topology.ActualCuspCentralFiberRetraction
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.CWComplex.Classical.Basic

/-!
# Established strong-deformation-retract principles

This file isolates two standard general-topology results not currently packaged in Mathlib: the
upgrade from a cofibrant homotopy-equivalent inclusion to a strong deformation retract, and the
equivariant lift of such a retraction through a regular covering.  Their hypotheses contain the
full homotopy-extension and quotient-covering data used below.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace SphereSixComplex

/-- The continuous inclusion of a subspace. -/
public def topologicalSubsetInclusionMap {X : Type*} [TopologicalSpace X] (A : Set X) : C(A, X) where
  toFun := Subtype.val
  continuous_toFun := continuous_subtype_val

/-- The homotopy-extension property for the inclusion `A ⊆ X`. -/
public def HasHomotopyExtensionProperty {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∀ (Y : Type) (_ : TopologicalSpace Y) (f : C(X, Y)) (g : C(A, Y))
    (h : ContinuousMap.Homotopy (f.comp (topologicalSubsetInclusionMap A)) g),
    ∃ (f₁ : C(X, Y)) (H : ContinuousMap.Homotopy f f₁),
      ∀ s (a : A), H (s, (a : X)) = h (s, a)

/-- The inclusion `A ⊆ X` is a homotopy equivalence, with its inverse map recorded explicitly. -/
public def IsHomotopyEquivalenceInclusion {X : Type*} [TopologicalSpace X] (A : Set X) : Prop :=
  ∃ e : X ≃ₕ A, e.invFun = topologicalSubsetInclusionMap A

/-- A non-equivariant strong deformation retraction onto a subspace. -/
public structure StrongDeformationRetraction (X : Type*) [TopologicalSpace X] (A : Set X) where
  retract : C(X, X)
  homotopy : ContinuousMap.Homotopy (ContinuousMap.id X) retract
  retract_mem : ∀ x, retract x ∈ A
  retract_fixed : ∀ x, x ∈ A → retract x = x
  homotopy_fixed : ∀ s x, x ∈ A → homotopy (s, x) = x

namespace EstablishedGeneralTopology

/-- The inclusion of the base of a relative CW complex has the homotopy-extension property. -/
public axiom hasHomotopyExtensionProperty_of_relativeCWComplex
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (hCW : RelCWComplex (Set.univ : Set X) A) :
    HasHomotopyExtensionProperty A

/-- If a regular covering and the full inverse image of a subspace are contractible, their
quotients are `K(G,1)` spaces. For a relative CW pair, the subspace inclusion is therefore a
homotopy equivalence. -/
public axiom isHomotopyEquivalenceInclusion_of_contractible_regularCover
    {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] (p : C(E, B)) (A : Set E) (D : Set B)
    (hp : IsQuotientCoveringMap p G) (hpreimage : p ⁻¹' D = A)
    (hE : ContractibleSpace E) (hA : ContractibleSpace A)
    (hCW : RelCWComplex (Set.univ : Set B) D) :
    IsHomotopyEquivalenceInclusion D

/-- A cofibrant inclusion which is a homotopy equivalence is the inclusion of a strong
deformation retract. This is the standard homotopy-extension-property theorem. -/
public axiom strongDeformationRetraction_of_cofibration_homotopyEquivalence
    {X : Type*} [TopologicalSpace X] (A : Set X)
    (hHEP : HasHomotopyExtensionProperty A)
    (hEquiv : IsHomotopyEquivalenceInclusion A) :
    Nonempty (StrongDeformationRetraction X A)

/-- A strong deformation retraction lifts uniquely through a regular quotient covering. The
lift is equivariant under the deck group and retracts onto the full inverse image of the base
retract. -/
public axiom equivariantStrongDeformationRetraction_lift
    {G E B : Type*} [Group G] [TopologicalSpace E] [TopologicalSpace B]
    [MulAction G E] (p : C(E, B)) (A : Set E) (D : Set B)
    (hp : IsQuotientCoveringMap p G) (hpreimage : p ⁻¹' D = A)
    (R : StrongDeformationRetraction B D) :
    Nonempty (EquivariantStrongDeformationRetraction G E A)

end EstablishedGeneralTopology

end SphereSixComplex
