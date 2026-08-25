module

public import SphereSixComplex.Topology.SmoothRecognition
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Oriented marked smooth homotopy six-spheres

This file packages the geometric objects underlying the classical group `Θ₆`.  A *marking* is an
actual homotopy equivalence with the standard sphere.  Classically its degree is `+1` or `-1` and
therefore determines an orientation.  Mathlib does not yet define orientations of manifolds or the
degree of a map between manifolds, so retaining the marking is the strongest concrete replacement
currently available for an oriented homotopy sphere.

This is deliberately different from an unoriented diffeomorphism class of smooth structures on a
topological sphere.  No quotient and no h-cobordism theorem is introduced here.
-/

@[expose] public section

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- A closed smooth homotopy six-sphere with a chosen homotopy marking to the standard sphere.

The explicit marking is the formal orientation datum: replacing it by its composite with the
antipodal map reverses the induced classical orientation.  The Hausdorff and countability fields
record the hypotheses used by the classical differential-topology theorems. -/
public structure OrientedMarkedSmoothHomotopySixSphere.{u} where
  /-- The underlying carrier. -/
  carrier : Type u
  /-- Topology of the carrier. -/
  [topologicalSpace : TopologicalSpace carrier]
  /-- Smooth atlas modelled on real six-space. -/
  [chartedSpace : ChartedSpace RealModel carrier]
  /-- Classical manifolds are Hausdorff. -/
  [t2Space : T2Space carrier]
  /-- Classical manifolds are second countable. -/
  [secondCountableTopology : SecondCountableTopology carrier]
  /-- The given atlas is smooth. -/
  [isManifold : IsManifold 𝓘(ℝ, RealModel) ∞ carrier]
  /-- The homotopy sphere is compact. -/
  [compactSpace : CompactSpace carrier]
  /-- The homotopy sphere is connected. -/
  [connectedSpace : ConnectedSpace carrier]
  /-- The ends used in h-cobordisms are closed manifolds. -/
  [boundaryless : BoundarylessManifold 𝓘(ℝ, RealModel) carrier]
  /-- The marking whose degree determines the orientation. -/
  marking : carrier ≃ₕ SixSphere

namespace OrientedMarkedSmoothHomotopySixSphere

instance (S : OrientedMarkedSmoothHomotopySixSphere) : TopologicalSpace S.carrier :=
  S.topologicalSpace
instance (S : OrientedMarkedSmoothHomotopySixSphere) : ChartedSpace RealModel S.carrier :=
  S.chartedSpace
instance (S : OrientedMarkedSmoothHomotopySixSphere) : T2Space S.carrier := S.t2Space
instance (S : OrientedMarkedSmoothHomotopySixSphere) : SecondCountableTopology S.carrier :=
  S.secondCountableTopology
instance (S : OrientedMarkedSmoothHomotopySixSphere) : IsManifold 𝓘(ℝ, RealModel) ∞ S.carrier :=
  S.isManifold
instance (S : OrientedMarkedSmoothHomotopySixSphere) : CompactSpace S.carrier := S.compactSpace
instance (S : OrientedMarkedSmoothHomotopySixSphere) : ConnectedSpace S.carrier := S.connectedSpace
instance (S : OrientedMarkedSmoothHomotopySixSphere) :
    BoundarylessManifold 𝓘(ℝ, RealModel) S.carrier :=
  S.boundaryless

/-- Forgetting the explicit marking gives the recognition layer's smooth homotopy-sphere
contract. -/
public theorem smoothHomotopySixSphere (S : OrientedMarkedSmoothHomotopySixSphere) :
    SmoothHomotopySixSphere S.carrier where
  isManifold := inferInstance
  compact := inferInstance
  connected := inferInstance
  homotopyEquiv := ⟨S.marking⟩

/-- The standard marked sphere. -/
public def standard : OrientedMarkedSmoothHomotopySixSphere where
  carrier := SixSphere
  connectedSpace := sixSphere_connectedSpace
  marking := ContinuousMap.HomotopyEquiv.refl SixSphere

/-- The antipodal self-homeomorphism of the standard sphere, regarded as a homotopy
equivalence.  Classically this map has degree `-1` in dimension six. -/
public def antipodalMarking : SixSphere ≃ₕ SixSphere :=
  (Homeomorph.neg SixSphere).toHomotopyEquiv

@[simp]
public theorem antipodalMarking_apply (x : SixSphere) : antipodalMarking x = -x :=
  rfl

/-- Reverse the orientation represented by a marking by postcomposing it with the antipodal map
of `S⁶`.  This changes no underlying smooth-manifold data. -/
public def reverseOrientation (S : OrientedMarkedSmoothHomotopySixSphere) :
    OrientedMarkedSmoothHomotopySixSphere where
  carrier := S.carrier
  marking := S.marking.trans antipodalMarking

@[simp]
public theorem reverseOrientation_carrier (S : OrientedMarkedSmoothHomotopySixSphere) :
    S.reverseOrientation.carrier = S.carrier :=
  rfl

/-- The presently missing degree theory for self-homotopy equivalences of `S⁶`.

The composition law and the assertion that every self-equivalence has degree `±1` prevent this
from being a bare label for the desired antipodal conclusion.  A future implementation should
construct `degree` from the induced map on top integral homology. -/
public structure SixSphereDegreeTheory where
  /-- Degree of a self-homotopy equivalence. -/
  degree : (SixSphere ≃ₕ SixSphere) → ℤ
  /-- The identity has degree one. -/
  degree_refl : degree (ContinuousMap.HomotopyEquiv.refl SixSphere) = 1
  /-- Degree is multiplicative under composition. -/
  degree_trans : ∀ f g, degree (f.trans g) = degree f * degree g
  /-- Every homotopy equivalence has degree `±1`. -/
  degree_eq_one_or_neg_one : ∀ f, degree f = 1 ∨ degree f = -1
  /-- The antipodal equivalence has degree `-1` in even sphere dimension. -/
  degree_antipodal : degree antipodalMarking = -1
  /-- Homotopic self-maps have the same degree. -/
  degree_homotopic : ∀ f g : SixSphere ≃ₕ SixSphere,
    f.toFun.Homotopic g.toFun → degree f = degree g

/-- Availability of degree theory, isolated as a named proposition rather than an axiom. -/
public def SixSphereDegreeTheoryObligation : Prop := Nonempty SixSphereDegreeTheory

/-- Two markings of the same homotopy sphere induce the same orientation when their transition
self-equivalence of `S⁶` has degree one. -/
public def SameOrientation (D : SixSphereDegreeTheory) {X : Type*} [TopologicalSpace X]
    (e₁ e₂ : X ≃ₕ SixSphere) : Prop :=
  D.degree (e₁.symm.trans e₂) = 1

namespace SameOrientation

/-- Homotopic markings induce the same orientation. -/
public theorem of_homotopic (D : SixSphereDegreeTheory) {X : Type*} [TopologicalSpace X]
    {e₁ e₂ : X ≃ₕ SixSphere} (h : e₁.toFun.Homotopic e₂.toFun) :
    SameOrientation D e₁ e₂ := by
  unfold SameOrientation
  have htransition : (e₁.symm.trans e₂).toFun.Homotopic
      (ContinuousMap.HomotopyEquiv.refl SixSphere).toFun :=
    (ContinuousMap.Homotopic.comp h.symm (.refl e₁.invFun)).trans e₁.right_inv
  rw [D.degree_homotopic _ _ htransition]
  exact D.degree_refl

/-- A marking induces the same orientation as itself. -/
public theorem refl (D : SixSphereDegreeTheory) {X : Type*} [TopologicalSpace X]
    (e : X ≃ₕ SixSphere) : SameOrientation D e e := by
  unfold SameOrientation
  rw [D.degree_homotopic (e.symm.trans e)
    (ContinuousMap.HomotopyEquiv.refl SixSphere) e.right_inv]
  exact D.degree_refl

/-- Reversing the comparison of two markings preserves the same-orientation condition. -/
public theorem symm (D : SixSphereDegreeTheory) {X : Type*} [TopologicalSpace X]
    {e₁ e₂ : X ≃ₕ SixSphere} (h : SameOrientation D e₁ e₂) :
    SameOrientation D e₂ e₁ := by
  let f := e₁.symm.trans e₂
  have hf : D.degree f = 1 := h
  have hfinv : D.degree f.symm = 1 := by
    calc
      D.degree f.symm = D.degree f * D.degree f.symm := by rw [hf, one_mul]
      _ = D.degree (f.trans f.symm) := (D.degree_trans f f.symm).symm
      _ = D.degree (ContinuousMap.HomotopyEquiv.refl SixSphere) :=
        D.degree_homotopic _ _ f.left_inv
      _ = 1 := D.degree_refl
  exact hfinv

/-- Same orientation is transitive on markings of a fixed homotopy sphere. -/
public theorem trans (D : SixSphereDegreeTheory) {X : Type*} [TopologicalSpace X]
    {e₁ e₂ e₃ : X ≃ₕ SixSphere}
    (h₁₂ : SameOrientation D e₁ e₂) (h₂₃ : SameOrientation D e₂ e₃) :
    SameOrientation D e₁ e₃ := by
  let f₁₂ := e₁.symm.trans e₂
  let f₂₃ := e₂.symm.trans e₃
  have hcomp : D.degree (f₁₂.trans f₂₃) = 1 := by
    rw [D.degree_trans, show D.degree f₁₂ = 1 from h₁₂,
      show D.degree f₂₃ = 1 from h₂₃, one_mul]
  have hcancel : (f₁₂.trans f₂₃).toFun.Homotopic
      (e₁.symm.trans e₃).toFun := by
    exact ContinuousMap.Homotopic.comp (.refl e₃.toFun)
      (ContinuousMap.Homotopic.comp e₂.left_inv (.refl e₁.invFun))
  exact (D.degree_homotopic _ _ hcancel).symm.trans hcomp

/-- Precomposing both markings by a homotopy equivalence does not change their relative
orientation. -/
public theorem precomp (D : SixSphereDegreeTheory)
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e₁ e₂ : X ≃ₕ SixSphere} (a : Y ≃ₕ X) (h : SameOrientation D e₁ e₂) :
    SameOrientation D (a.trans e₁) (a.trans e₂) := by
  unfold SameOrientation at h ⊢
  have hcancel : ((a.trans e₁).symm.trans (a.trans e₂)).toFun.Homotopic
      (e₁.symm.trans e₂).toFun := by
    exact ContinuousMap.Homotopic.comp (.refl e₂.toFun)
      (ContinuousMap.Homotopic.comp a.right_inv (.refl e₁.invFun))
  rw [D.degree_homotopic _ _ hcancel]
  exact h

/-- Postcomposition with the antipodal map genuinely reverses the orientation represented by a
marking. -/
public theorem not_reverseOrientation (D : SixSphereDegreeTheory)
    (S : OrientedMarkedSmoothHomotopySixSphere) :
    ¬ SameOrientation D S.marking S.reverseOrientation.marking := by
  unfold SameOrientation
  have hcancel :
      (S.marking.symm.trans S.reverseOrientation.marking).toFun.Homotopic
        antipodalMarking.toFun := by
    exact ContinuousMap.Homotopic.comp (.refl antipodalMarking.toFun) S.marking.right_inv
  rw [D.degree_homotopic _ _ hcancel, D.degree_antipodal]
  norm_num

end SameOrientation

end OrientedMarkedSmoothHomotopySixSphere

end SphereSixComplex
