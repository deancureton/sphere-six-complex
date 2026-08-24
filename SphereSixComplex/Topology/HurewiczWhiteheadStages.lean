/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.HurewiczWhitehead
public import SphereSixComplex.Topology.SingularHomologyDegreeZero
public import SphereSixComplex.Topology.SphereFiniteCWModel
public import SphereSixComplex.Topology.StandardSpherePositiveHomology
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Direction-correct Hurewicz--Whitehead recognition stages

The Hurewicz comparison map has direction `S⁶ → X`: a top-dimensional spherical class is
represented by a map out of the sphere. Degree-zero naturality and the degree-six generator then
detect a homology equivalence. A homological Whitehead theorem realizes that same map, whose
inverse has the recognition direction `X → S⁶`.

This file ports the proved recognition boundary and classical CW bookkeeping from the companion
formalization. It makes no Hurewicz, manifold-CW, or homological Whitehead assumption.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits ContinuousMap Topology

namespace SphereSixComplex

/-- A representative of the top-dimensional class whose map on sixth integral homology is an
isomorphism. Its direction is necessarily from the standard sphere to the target. -/
public def HasTopDimensionalSphericalGenerator
    (X : Type) [TopologicalSpace X] : Prop :=
  ∃ f : C(SixSphere, X),
    IsIso (((singularHomologyFunctor AddCommGrpCat 6).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f))

/-- A coherent comparison map in the direction supplied by the Hurewicz theorem. -/
public def HasIntegralHomologyComparisonFromSixSphere
    (X : Type) [TopologicalSpace X] : Prop :=
  ∃ f : C(SixSphere, X), IsIntegralHomologyEquivalence f

private theorem subsingleton_of_addEquiv
    {A B : Type*} [Add A] [Add B] (e : A ≃+ B) [Subsingleton B] : Subsingleton A :=
  ⟨fun _ _ ↦ e.injective (Subsingleton.elim _ _)⟩

/-- For spaces with the integral homology of `S⁶`, the maps in degrees zero and six detect an
integral homology equivalence. Vanishing in the other degrees comes from the explicit sphere
calculation rather than from the tautological comparison predicate alone. -/
public theorem isIntegralHomologyEquivalence_of_sixSphere_zero_six
    {X : Type} [TopologicalSpace X]
    (hSphere : SixSpherePositiveHomologyInputs)
    (hX : HasIntegralHomologyOfSixSphere X) (f : C(SixSphere, X))
    (hZero : IsIso (((singularHomologyFunctor AddCommGrpCat 0).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)))
    (hSix : IsIso (((singularHomologyFunctor AddCommGrpCat 6).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f))) :
    IsIntegralHomologyEquivalence f := by
  intro k
  by_cases hkZero : k = 0
  · subst k
    exact hZero
  by_cases hkSix : k = 6
  · subst k
    exact hSix
  · let _ : Subsingleton (IntegralSingularHomology k SixSphere) :=
      hSphere.otherDegrees k hkZero hkSix
    obtain ⟨eX⟩ := hX k
    let _ : Subsingleton (IntegralSingularHomology k X) :=
      subsingleton_of_addEquiv eX
    exact IsZero.isIso (AddCommGrpCat.isZero_of_subsingleton _)
      (AddCommGrpCat.isZero_of_subsingleton _) _

/-- A top-dimensional generator gives the direction-correct homology comparison. The degree-zero
map is an isomorphism by the proved naturality of the singular-homology augmentation. -/
public theorem HasTopDimensionalSphericalGenerator.homologyComparison
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (h : HasTopDimensionalSphericalGenerator X)
    (hSphere : SixSpherePositiveHomologyInputs)
    (hX : HasIntegralHomologyOfSixSphere X) :
    HasIntegralHomologyComparisonFromSixSphere X := by
  obtain ⟨f, hSix⟩ := h
  let _ : PathConnectedSpace SixSphere := sixSphere_pathConnectedSpace
  have hZero : IsIso (((singularHomologyFunctor AddCommGrpCat 0).obj
      (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f)) :=
    integralSingularHomologyMap_zero_isIso (TopCat.ofHom f)
  exact ⟨f, isIntegralHomologyEquivalence_of_sixSphere_zero_six
    hSphere hX f hZero hSix⟩

/-- The identity map is a top-dimensional spherical generator for the standard sphere. -/
public theorem sixSphere_hasTopDimensionalSphericalGenerator :
    HasTopDimensionalSphericalGenerator SixSphere :=
  ⟨ContinuousMap.id SixSphere, (isIntegralHomologyEquivalence_id SixSphere) 6⟩

/-- Postcomposition with a homotopy equivalence preserves a top-dimensional generator. -/
public theorem HasTopDimensionalSphericalGenerator.postcompHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (h : HasTopDimensionalSphericalGenerator X) (e : X ≃ₕ Y) :
    HasTopDimensionalSphericalGenerator Y := by
  obtain ⟨f, hf⟩ := h
  refine ⟨e.toFun.comp f, ?_⟩
  let _ := hf
  let _ := (homotopyEquiv_isIntegralHomologyEquivalence e) 6
  change IsIso (((singularHomologyFunctor AddCommGrpCat 6).obj
    (AddCommGrpCat.of ℤ)).map (TopCat.ofHom f ≫ TopCat.ofHom e.toFun))
  rw [Functor.map_comp]
  infer_instance

/-- A concrete classical CW complex having the homotopy type of a space. -/
public structure ClassicalCWModel (X : Type) [TopologicalSpace X] where
  /-- The carrier of the CW model. -/
  Carrier : Type
  /-- The topology on the model. -/
  topology : TopologicalSpace Carrier
  /-- Its classical CW structure. -/
  cwComplex : @CWComplex Carrier topology (Set.univ : Set Carrier)
  /-- The specified homotopy equivalence to the model. -/
  homotopyEquiv : Nonempty (@ContinuousMap.HomotopyEquiv X Carrier inferInstance topology)

/-- A space has classical CW type if it admits a concrete classical CW model. -/
public def HasClassicalCWType (X : Type) [TopologicalSpace X] : Prop :=
  Nonempty (ClassicalCWModel X)

/-- A space carrying a classical CW structure is its own CW model. -/
public theorem hasClassicalCWType_of_cwComplex
    (X : Type) [TopologicalSpace X] [CWComplex (Set.univ : Set X)] :
    HasClassicalCWType X :=
  ⟨⟨X, inferInstance, inferInstance, ⟨ContinuousMap.HomotopyEquiv.refl X⟩⟩⟩

/-- Precomposing a CW model with a homotopy equivalence transports classical CW type. -/
public theorem hasClassicalCWType_precomp_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (hY : HasClassicalCWType Y) : HasClassicalCWType X := by
  obtain ⟨M⟩ := hY
  obtain ⟨hM⟩ := M.homotopyEquiv
  let _ : TopologicalSpace M.Carrier := M.topology
  exact ⟨{
    Carrier := M.Carrier
    topology := M.topology
    cwComplex := M.cwComplex
    homotopyEquiv := ⟨e.trans hM⟩
  }⟩

/-- Classical CW type is invariant under homotopy equivalence. -/
public theorem hasClassicalCWType_iff_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) :
    HasClassicalCWType X ↔ HasClassicalCWType Y :=
  ⟨hasClassicalCWType_precomp_homotopyEquiv e.symm,
    hasClassicalCWType_precomp_homotopyEquiv e⟩

/-- The explicit finite two-cell model gives the standard six-sphere classical CW type. -/
public theorem sixSphere_hasClassicalCWType : HasClassicalCWType SixSphere := by
  exact ⟨{
    Carrier := SixSphereFiniteCWCarrier
    topology := inferInstance
    cwComplex := sixSphereFiniteCWComplex
    homotopyEquiv := ⟨sixSphereFiniteCWHomeomorph.symm.toHomotopyEquiv⟩
  }⟩

/-- The unresolved homological Whitehead theorem, restricted to spaces of classical CW type. -/
public def ClassicalCWIntegralHomologyWhiteheadProperty
    (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] : Prop :=
  HasClassicalCWType X → HasClassicalCWType Y →
    IntegralHomologyWhiteheadProperty X Y

/-- Whitehead applied to a comparison `S⁶ → X` gives the recognition equivalence in the
reverse direction `X ≃ₕ S⁶`. -/
public theorem homotopyEquivSixSphere_of_reverseComparison_of_whitehead
    {X : Type} [TopologicalSpace X]
    (hComparison : HasIntegralHomologyComparisonFromSixSphere X)
    (hWhitehead : IntegralHomologyWhiteheadProperty SixSphere X) :
    Nonempty (X ≃ₕ SixSphere) := by
  obtain ⟨f, hf⟩ := hComparison
  obtain ⟨e, -⟩ := hWhitehead f hf
  exact ⟨e.symm⟩

/-- The complete direction-correct boundary: Hurewicz supplies a spherical generator, the
zero/six detector supplies a homology equivalence, and CW Whitehead reverses the resulting
homotopy equivalence. -/
public theorem homotopyEquivSixSphere_of_sphericalGenerator_of_classicalCWWhitehead
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (hSphere : SixSpherePositiveHomologyInputs)
    (hX : HasIntegralHomologyOfSixSphere X)
    (hGenerator : HasTopDimensionalSphericalGenerator X)
    (hCWX : HasClassicalCWType X)
    (hWhitehead : ClassicalCWIntegralHomologyWhiteheadProperty SixSphere X) :
    Nonempty (X ≃ₕ SixSphere) :=
  homotopyEquivSixSphere_of_reverseComparison_of_whitehead
    (hGenerator.homologyComparison hSphere hX)
    (hWhitehead sixSphere_hasClassicalCWType hCWX)

end SphereSixComplex
