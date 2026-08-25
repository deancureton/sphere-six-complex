/-
Copyright (c) 2026 Paul Lezeau. All rights reserved.
Released under Apache 2.0 license as described in the source repository's LICENSE file.
Authors: Paul Lezeau
-/
module

public import SphereSixComplex.Topology.SmoothRecognitionFoundations

/-!
# Smooth six-sphere classification interfaces

This file separates the formal quotient argument in the classical smooth Poincare proof from the
missing differential topology. A marked smooth six-sphere is a smooth real six-manifold together
with a homeomorphism to the standard sphere. Diffeomorphism is an equivalence relation, so smooth
structures form an honest quotient type.

Pinned Mathlib has no smooth h-cobordism API and no formal computation of `Theta_6`. The structure
`SmoothHCobordismRelation` therefore exposes only the relational input needed to state those two
classical stages. No h-cobordism or classification theorem is assumed in this file.
-/

@[expose] public section

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Smale's generalized topological Poincare theorem in dimension six. -/
public def GeneralizedTopologicalPoincareSix : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M],
    Nonempty (M ≃ₕ SixSphere) → Nonempty (M ≃ₜ SixSphere)

/-- The standard-model smooth Poincare theorem in dimension six. -/
public def SmoothPoincareSixStandardModel : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M],
    Nonempty (M ≃ₕ SixSphere) → SmoothDiffeomorphicToSixSphere M

/-- Smooth Poincare in dimension six implies generalized topological Poincare in dimension six. -/
public theorem generalizedTopologicalPoincareSix_of_smoothPoincareSixStandardModel
    (hSmooth : SmoothPoincareSixStandardModel) : GeneralizedTopologicalPoincareSix := by
  intro M _ _ _ _ _ _ hHomotopy
  obtain ⟨d⟩ := hSmooth M hHomotopy
  exact ⟨d.toHomeomorph⟩

/-- A smooth real six-manifold whose underlying topological space is the standard six-sphere. -/
public structure MarkedSmoothSixSphere where
  Carrier : Type
  [topology : TopologicalSpace Carrier]
  [chartedSpace : ChartedSpace RealModel Carrier]
  [isManifold : IsManifold 𝓘(ℝ, RealModel) ∞ Carrier]
  homeomorph : Nonempty (Carrier ≃ₜ SixSphere)

namespace MarkedSmoothSixSphere

public instance (X : MarkedSmoothSixSphere) : TopologicalSpace X.Carrier := X.topology

public instance (X : MarkedSmoothSixSphere) : ChartedSpace RealModel X.Carrier := X.chartedSpace

public instance (X : MarkedSmoothSixSphere) : IsManifold 𝓘(ℝ, RealModel) ∞ X.Carrier :=
  X.isManifold

/-- Two marked smooth spheres are equivalent when their smooth manifolds are diffeomorphic. -/
public def Diffeomorphic (X Y : MarkedSmoothSixSphere) : Prop :=
  Nonempty (Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X.Carrier Y.Carrier ∞)

public theorem diffeomorphic_refl (X : MarkedSmoothSixSphere) : X.Diffeomorphic X :=
  ⟨Diffeomorph.refl 𝓘(ℝ, RealModel) X.Carrier ∞⟩

public theorem diffeomorphic_symm {X Y : MarkedSmoothSixSphere}
    (h : X.Diffeomorphic Y) : Y.Diffeomorphic X := by
  obtain ⟨d⟩ := h
  exact ⟨d.symm⟩

public theorem diffeomorphic_trans {X Y Z : MarkedSmoothSixSphere}
    (hXY : X.Diffeomorphic Y) (hYZ : Y.Diffeomorphic Z) : X.Diffeomorphic Z := by
  obtain ⟨dXY⟩ := hXY
  obtain ⟨dYZ⟩ := hYZ
  exact ⟨dXY.trans dYZ⟩

/-- Diffeomorphism is an equivalence relation on marked smooth six-spheres. -/
public def diffeomorphismSetoid : Setoid MarkedSmoothSixSphere where
  r := Diffeomorphic
  iseqv :=
    ⟨diffeomorphic_refl, fun {_ _} h ↦ diffeomorphic_symm h,
      fun {_ _ _} hXY hYZ ↦ diffeomorphic_trans hXY hYZ⟩

/-- The quotient type of unoriented smooth structures on a topological six-sphere. -/
public abbrev DiffeomorphismClass := Quotient diffeomorphismSetoid

/-- The diffeomorphism class represented by a marked smooth sphere. -/
public def classOf (X : MarkedSmoothSixSphere) : DiffeomorphismClass :=
  Quotient.mk diffeomorphismSetoid X

/-- The standard sphere with its canonical smooth structure and marking. -/
public noncomputable def standard : MarkedSmoothSixSphere where
  Carrier := SixSphere
  topology := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  homeomorph := ⟨Homeomorph.refl SixSphere⟩

/-- The set-level consequence of `Theta_6 = 0` needed here. -/
public def DiffeomorphismClassesTrivial : Prop :=
  Subsingleton DiffeomorphismClass

public theorem diffeomorphic_standard_of_classes_trivial
    (h : DiffeomorphismClassesTrivial) (X : MarkedSmoothSixSphere) :
    X.Diffeomorphic standard := by
  change diffeomorphismSetoid.r X standard
  apply Quotient.exact
  exact @Subsingleton.elim DiffeomorphismClass h (classOf X) (classOf standard)

end MarkedSmoothSixSphere

/-- Smooth Poincare in dimension six makes the smooth-structure quotient of the topological
six-sphere trivial. -/
public theorem markedSmoothSixSphereClassesTrivial_of_smoothPoincareSixStandardModel
    (hSmooth : SmoothPoincareSixStandardModel) :
    MarkedSmoothSixSphere.DiffeomorphismClassesTrivial := by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  apply Quotient.sound
  obtain ⟨eX⟩ := X.homeomorph
  obtain ⟨eY⟩ := Y.homeomorph
  let _ : T2Space X.Carrier := eX.symm.t2Space
  let _ : SecondCountableTopology X.Carrier := eX.secondCountableTopology
  let _ : CompactSpace X.Carrier := eX.symm.compactSpace
  let _ : T2Space Y.Carrier := eY.symm.t2Space
  let _ : SecondCountableTopology Y.Carrier := eY.secondCountableTopology
  let _ : CompactSpace Y.Carrier := eY.symm.compactSpace
  obtain ⟨dX⟩ := hSmooth X.Carrier ⟨eX.toHomotopyEquiv⟩
  obtain ⟨dY⟩ := hSmooth Y.Carrier ⟨eY.toHomotopyEquiv⟩
  exact ⟨dX.trans dY.symm⟩

/-- A relation that an eventual geometric theory may instantiate by smooth h-cobordism. -/
public structure SmoothHCobordismRelation where
  setoid : Setoid MarkedSmoothSixSphere

namespace SmoothHCobordismRelation

/-- The quotient type of proposed h-cobordism classes. -/
public abbrev Class (H : SmoothHCobordismRelation) := Quotient H.setoid

/-- The h-cobordism theorem in the exact relational form used for smooth six-spheres. -/
public def HCobordismTheoremSix (H : SmoothHCobordismRelation) : Prop :=
  ∀ {X Y : MarkedSmoothSixSphere}, H.setoid.r X Y → X.Diffeomorphic Y

/-- The required set-level form of the computation `Theta_6 = 0`. -/
public def ThetaSixVanishes (H : SmoothHCobordismRelation) : Prop :=
  Subsingleton H.Class

/-- H-cobordism classification and `Theta_6 = 0` collapse diffeomorphism classes. -/
public theorem diffeomorphismClassesTrivial (H : SmoothHCobordismRelation)
    (hCobordism : H.HCobordismTheoremSix) (hTheta : H.ThetaSixVanishes) :
    MarkedSmoothSixSphere.DiffeomorphismClassesTrivial := by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  apply Quotient.sound
  apply hCobordism
  apply Quotient.exact
  exact @Subsingleton.elim H.Class hTheta
    (Quotient.mk H.setoid X) (Quotient.mk H.setoid Y)

end SmoothHCobordismRelation

/-- Triviality of smooth-structure classes supplies the fixed-space no-exotic-sphere obligation. -/
public theorem homeomorphismToDiffeomorphismSixSphere_of_classes_trivial
    (hClasses : MarkedSmoothSixSphere.DiffeomorphismClassesTrivial)
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X] :
    HomeomorphismToDiffeomorphismSixSphereObligation X := by
  intro hManifold hHomeomorph
  let X' : MarkedSmoothSixSphere :=
    { Carrier := X
      topology := inferInstance
      chartedSpace := inferInstance
      isManifold := hManifold
      homeomorph := hHomeomorph }
  exact MarkedSmoothSixSphere.diffeomorphic_standard_of_classes_trivial hClasses X'

/-- Smale plus triviality of smooth-structure classes proves smooth Poincare. -/
public theorem smoothPoincareSixStandardModel_of_classicalStages
    (hSmale : GeneralizedTopologicalPoincareSix)
    (hClasses : MarkedSmoothSixSphere.DiffeomorphismClassesTrivial) :
    SmoothPoincareSixStandardModel := by
  intro M _ _ _ _ _ _ hHomotopy
  exact homeomorphismToDiffeomorphismSixSphere_of_classes_trivial hClasses
    inferInstance (hSmale M hHomotopy)

/-- The three classical inputs imply the fixed-space smooth-recognition obligation. -/
public theorem homotopyToDiffeomorphismSixSphere_of_classicalStages
    (hSmale : GeneralizedTopologicalPoincareSix)
    (H : SmoothHCobordismRelation) (hCobordism : H.HCobordismTheoremSix)
    (hTheta : H.ThetaSixVanishes)
    {X : Type} [TopologicalSpace X] [ChartedSpace RealModel X]
    [T2Space X] [SecondCountableTopology X] [CompactSpace X] :
    HomotopyToDiffeomorphismSixSphereObligation X := by
  intro hManifold hHomotopy
  exact smoothPoincareSixStandardModel_of_classicalStages hSmale
    (H.diffeomorphismClassesTrivial hCobordism hTheta) X hHomotopy

end SphereSixComplex
