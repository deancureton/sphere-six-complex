module

public import SphereSixComplex.Topology.HurewiczWhitehead
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Foundations for smooth recognition in dimension six

This file records the part of the recognition argument that can be proved with the current
mathlib API and separates the remaining classical theorems along their mathematical boundaries.

Mathlib defines cubical higher homotopy groups, but currently has no functorial maps on those
groups, Hurewicz homomorphism, homological Whitehead theorem for spaces of CW type, or theorem
that manifolds have CW type.  Its Poincare-conjecture file states, but does not prove, the relevant
topological and smooth recognition theorems.  Mathlib also has no h-cobordism theorem or
formalization of the Kervaire--Milnor computation that the group of smooth homotopy six-spheres is
trivial.  Consequently those results cannot yet be discharged from existing library theorems.

The results below are not new recognition assumptions in disguise.  They prove two concrete
facts: simple connectivity kills the zeroth and first homotopy groups in mathlib's actual cubical
model, and the smooth Poincare step factors exactly into topological Poincare followed by the
nonexistence of exotic smooth structures on the topological six-sphere.
-/

@[expose] public section

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

/-- A simply connected integral homology six-sphere has only one path component, expressed in
mathlib's cubical zeroth homotopy type. -/
public theorem SmoothSimplyConnectedIntegralHomologySixSphere.homotopyGroup_zero_subsingleton
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothSimplyConnectedIntegralHomologySixSphere X) (x : X) :
    Subsingleton (π_ 0 X x) := by
  let _ : SimplyConnectedSpace X := h.simplyConnected
  exact HomotopyGroup.pi0EquivZerothHomotopy.subsingleton

/-- A simply connected integral homology six-sphere has trivial first homotopy group in
mathlib's cubical model. -/
public theorem SmoothSimplyConnectedIntegralHomologySixSphere.homotopyGroup_one_subsingleton
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothSimplyConnectedIntegralHomologySixSphere X) (x : X) :
    Subsingleton (π_ 1 X x) := by
  let _ : SimplyConnectedSpace X := h.simplyConnected
  exact HomotopyGroup.pi1EquivFundamentalGroup.subsingleton

/-- The zeroth homotopy type of a simply connected integral homology six-sphere is a point. -/
public noncomputable def
    SmoothSimplyConnectedIntegralHomologySixSphere.homotopyGroup_zero_equiv_pUnit
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothSimplyConnectedIntegralHomologySixSphere X) (x : X) :
    π_ 0 X x ≃ PUnit := by
  let _ : Subsingleton (π_ 0 X x) := h.homotopyGroup_zero_subsingleton x
  exact Equiv.punitOfNonemptyOfSubsingleton

/-- The first homotopy group of a simply connected integral homology six-sphere is a point. -/
public noncomputable def
    SmoothSimplyConnectedIntegralHomologySixSphere.homotopyGroup_one_equiv_pUnit
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothSimplyConnectedIntegralHomologySixSphere X) (x : X) :
    π_ 1 X x ≃ PUnit := by
  let _ : Subsingleton (π_ 1 X x) := h.homotopyGroup_one_subsingleton x
  exact Equiv.punitOfNonemptyOfSubsingleton

/-- Every element of the first homotopy group is the identity. -/
public theorem SmoothSimplyConnectedIntegralHomologySixSphere.homotopyGroup_one_eq_one
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (h : SmoothSimplyConnectedIntegralHomologySixSphere X) (x : X) (g : π_ 1 X x) :
    g = 1 := by
  let _ : Subsingleton (π_ 1 X x) := h.homotopyGroup_one_subsingleton x
  exact Subsingleton.elim _ _

/-- The topological generalized Poincare step for a fixed smooth six-manifold. -/
public def HomotopyToHomeomorphismSixSphereObligation
    (X : Type) [TopologicalSpace X] [ChartedSpace RealModel X] : Prop :=
  IsManifold 𝓘(ℝ, RealModel) ∞ X → Nonempty (X ≃ₕ SixSphere) → Nonempty (X ≃ₜ SixSphere)

/-- The absence of an exotic smooth structure on a fixed topological six-sphere.  Globally, this
is the dimension-six Kervaire--Milnor input. -/
public def HomeomorphismToDiffeomorphismSixSphereObligation
    (X : Type) [TopologicalSpace X] [ChartedSpace RealModel X] : Prop :=
  IsManifold 𝓘(ℝ, RealModel) ∞ X →
    Nonempty (X ≃ₜ SixSphere) → SmoothDiffeomorphicToSixSphere X

/-- For a fixed carrier and atlas, the smooth Poincare theorem is exactly the conjunction of
topological Poincare and uniqueness of the smooth structure on the topological sphere. -/
public theorem homotopyToDiffeomorphismSixSphere_iff_topologicalPoincare_and_noExotic
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X] :
    HomotopyToDiffeomorphismSixSphereObligation X ↔
      HomotopyToHomeomorphismSixSphereObligation X ∧
        HomeomorphismToDiffeomorphismSixSphereObligation X := by
  constructor
  · intro h
    constructor
    · intro hM hE
      obtain ⟨d⟩ := h hM hE
      exact ⟨d.toHomeomorph⟩
    · intro hM hE
      obtain ⟨e⟩ := hE
      exact h hM ⟨e.toHomotopyEquiv⟩
  · rintro ⟨hTopological, hNoExotic⟩ hM hE
    exact hNoExotic hM (hTopological hM hE)

/-- The classical recognition route, with its three independent mathematical inputs made
explicit: Hurewicz--Whitehead, topological Poincare, and the dimension-six smooth-structure
classification. -/
public theorem smoothSixSphereRecognition_of_classical_factors
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (hWhitehead : HomologyToHomotopySixSphereObligation X)
    (hTopological : HomotopyToHomeomorphismSixSphereObligation X)
    (hNoExotic : HomeomorphismToDiffeomorphismSixSphereObligation X) :
    SmoothSixSphereRecognitionObligation X := by
  intro hX
  exact hNoExotic hX.isManifold (hTopological hX.isManifold (hWhitehead hX))

/-- A coherent homology comparison plus map-level Whitehead, topological Poincare, and the
dimension-six smooth-structure classification give the complete recognition theorem. -/
public theorem smoothSixSphereRecognition_of_comparison_whitehead_and_classification
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    (hComparison : SmoothSimplyConnectedIntegralHomologySixSphere X →
      HasIntegralHomologyComparisonToSixSphere X)
    (hWhitehead : IntegralHomologyWhiteheadProperty X SixSphere)
    (hTopological : HomotopyToHomeomorphismSixSphereObligation X)
    (hNoExotic : HomeomorphismToDiffeomorphismSixSphereObligation X) :
    SmoothSixSphereRecognitionObligation X :=
  smoothSixSphereRecognition_of_classical_factors
    (homologyToHomotopySixSphere_of_comparison_of_whitehead hComparison hWhitehead)
    hTopological hNoExotic

end SphereSixComplex
