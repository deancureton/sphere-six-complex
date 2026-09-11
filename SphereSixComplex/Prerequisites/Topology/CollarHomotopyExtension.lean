module

public import Mathlib.Geometry.Manifold.Bordism
public import Mathlib.Geometry.Manifold.Instances.Icc
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.Diffeomorph
public import SphereSixComplex.Prerequisites.Topology.MapHomotopyEquivalence
public import SphereSixComplex.Prerequisites.Topology.PushoutHomotopy

/-!
# Homotopy data supplied by an explicit collar

An explicit collar makes its zero section a strong deformation retract of the *collar
neighbourhood*.  This file records that fact in the form used by `PushoutHomotopy` and transports
it across the collar chart.  It also isolates the relative path-lifting property which is needed
to upgrade a homotopy-equivalent inclusion to a strong deformation retract of the whole ambient
space.

The local construction is completely explicit: at time `s`, the collar parameter `t` is replaced
by `s * t`.  No collar-gluing, cofibration, or homotopy-extension theorem is assumed.
-/

@[expose] public section

noncomputable section

open CategoryTheory ContinuousMap Function Set TopologicalSpace Topology
open scoped ContDiff Manifold Topology

namespace SphereSixComplex

universe u uE uH uM uW










variable {A X : TopCat.{u}} {i : A ⟶ X}












/-! ## The precise global homotopy-extension interface -/

variable {A₀ X₀ : Type u} [TopologicalSpace A₀] [TopologicalSpace X₀]

/-- Homotopy-extension data for a specified inclusion.  This is the usual HEP formulation: a
homotopy on the subspace which starts as the restriction of an ambient map extends to an ambient
homotopy, with equality on the subspace at every time.

It is kept as an explicit proposition because pinned Mathlib has no topological cofibration API. -/
public structure HomotopyExtensionProperty (i : C(A₀, X₀)) : Prop where
  extend : ∀ {Y : Type u} [TopologicalSpace Y]
      (f : C(X₀, Y)) {h₁ : C(A₀, Y)}
      (H : ContinuousMap.Homotopy (f.comp i) h₁),
    ∃ (f₁ : C(X₀, Y)) (F : ContinuousMap.Homotopy f f₁),
      ∀ (t : unitInterval) (a : A₀), F (t, i a) = H (t, a)

/-- A (not necessarily strong) deformation-retract package.  The endpoint homotopy need not fix
the image of the inclusion pointwise. -/
public structure DeformationRetractData (i : C(A₀, X₀)) where
  retraction : C(X₀, A₀)
  retract : retraction.comp i = ContinuousMap.id A₀
  homotopy : ContinuousMap.Homotopy
    (i.comp retraction) (ContinuousMap.id X₀)

namespace DeformationRetractData

variable {i₀ : C(A₀, X₀)} (D : DeformationRetractData i₀)

/-- A deformation retract whose homotopy fixes the included subspace gives the strong package
used by the pushout theorem. -/
public def toStrong
    (fixed : ∀ (t : unitInterval) (a : A₀), D.homotopy (t, i₀ a) = i₀ a) :
    TopCat.StrongDeformationRetractData (TopCat.ofHom i₀) where
  retraction := TopCat.ofHom D.retraction
  retract := by
    ext a
    exact ContinuousMap.congr_fun D.retract a
  homotopy := D.homotopy
  fixed := fixed

end DeformationRetractData

/-- HEP strictifies the inverse of a homotopy-equivalent inclusion and produces an ordinary
deformation retract.  The only datum still absent from a strong deformation retract is the
pointwise fixedness of the final homotopy. -/
public theorem HomotopyExtensionProperty.exists_deformationRetractData
    {i₀ : C(A₀, X₀)} (hep : HomotopyExtensionProperty i₀)
    (hi : IsHomotopyEquivalence i₀) :
    Nonempty (DeformationRetractData i₀) := by
  obtain ⟨e, he⟩ := hi
  have he' : e.toFun = i₀ := by
    ext a
    exact congrFun he a
  let L₀ : ContinuousMap.Homotopy (e.invFun.comp e.toFun) (ContinuousMap.id A₀) :=
    e.left_inv.some
  let L : ContinuousMap.Homotopy (e.invFun.comp i₀) (ContinuousMap.id A₀) :=
    L₀.cast (by rw [← he']) rfl
  obtain ⟨r, F, hF⟩ := hep.extend e.invFun L
  have hr : r.comp i₀ = ContinuousMap.id A₀ := by
    ext a
    calc
      r (i₀ a) = F (1, i₀ a) := (F.map_one_left (i₀ a)).symm
      _ = L (1, a) := hF 1 a
      _ = a := L.map_one_left a
  let K₀ : ContinuousMap.Homotopy (e.toFun.comp e.invFun) (ContinuousMap.id X₀) :=
    e.right_inv.some
  let K : ContinuousMap.Homotopy (i₀.comp e.invFun) (ContinuousMap.id X₀) :=
    K₀.cast (by rw [← he']) rfl
  let iF : ContinuousMap.Homotopy (i₀.comp e.invFun) (i₀.comp r) :=
    (ContinuousMap.Homotopy.refl i₀).comp F
  exact ⟨{
    retraction := r
    retract := hr
    homotopy := iF.symm.trans K }⟩


end SphereSixComplex
