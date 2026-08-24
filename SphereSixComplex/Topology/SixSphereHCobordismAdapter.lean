module

public import SphereSixComplex.Topology.SmoothHCobordism
public import SphereSixComplex.Topology.SmoothSixSphereClassification

/-!
# Adapter from geometric h-cobordisms to six-sphere classification

The recognition layer stores only a topological marking of a smooth six-manifold.  That marking
supplies compactness, Hausdorffness, and second countability, so the generic collared
h-cobordism relation applies to its carrier.

This file proves that the geometric relation is an equivalence relation and instantiates the
existing `SmoothHCobordismRelation` interface.  Transitivity uses the constructed three-piece
smooth collar gluing theorem.
-/

@[expose] public section

noncomputable section

open scoped ContDiff Manifold Topology

namespace SphereSixComplex

namespace MarkedSmoothSixSphere

/-- A chosen representative of the stored topological marking. -/
public noncomputable def chosenHomeomorph (X : MarkedSmoothSixSphere) :
    X.Carrier ≃ₜ SixSphere :=
  Classical.choice X.homeomorph

/-- Hausdorffness transported from the standard sphere. -/
public noncomputable instance (X : MarkedSmoothSixSphere) : T2Space X.Carrier :=
  X.chosenHomeomorph.symm.t2Space

/-- Second countability transported from the standard sphere. -/
public noncomputable instance (X : MarkedSmoothSixSphere) :
    SecondCountableTopology X.Carrier :=
  X.chosenHomeomorph.secondCountableTopology

/-- Compactness transported from the standard sphere. -/
public noncomputable instance (X : MarkedSmoothSixSphere) : CompactSpace X.Carrier :=
  X.chosenHomeomorph.symm.compactSpace

/-- The elementary geometric relation: existence of one smooth h-cobordism between the carriers.
It deliberately forgets the topological markings, matching the recognition layer's unoriented
compatibility object. -/
public def GeometricallyHCobordant (X Y : MarkedSmoothSixSphere) : Prop :=
  SmoothHCobordant 𝓘(ℝ, RealModel) X.Carrier Y.Carrier

/-- The geometric relation is reflexive by the explicit cylinder. -/
public theorem geometricallyHCobordant_refl (X : MarkedSmoothSixSphere) :
    X.GeometricallyHCobordant X :=
  SmoothHCobordant.refl 𝓘(ℝ, RealModel)

/-- The geometric relation is symmetric by reversal. -/
public theorem geometricallyHCobordant_symm {X Y : MarkedSmoothSixSphere}
    (h : X.GeometricallyHCobordant Y) : Y.GeometricallyHCobordant X :=
  SmoothHCobordant.symm 𝓘(ℝ, RealModel) h

/-- The geometric relation is transitive by smooth collar gluing. -/
public theorem geometricallyHCobordant_trans {X Y Z : MarkedSmoothSixSphere}
    (hXY : X.GeometricallyHCobordant Y) (hYZ : Y.GeometricallyHCobordant Z) :
    X.GeometricallyHCobordant Z :=
  SmoothHCobordant.trans 𝓘(ℝ, RealModel) hXY hYZ

/-- The smooth-gluing proposition specialized to topologically marked smooth six-spheres. -/
public def GeometricHCobordismGluingStatement : Prop :=
  ∀ X Y Z : MarkedSmoothSixSphere,
    SmoothHCobordant.GluingStatement 𝓘(ℝ, RealModel)
      (M₀ := X.Carrier) (M₁ := Y.Carrier) (M₂ := Z.Carrier)

/-- The constructed smooth collar gluing proves the specialized gluing proposition. -/
public theorem geometricHCobordismGluingStatement :
    GeometricHCobordismGluingStatement :=
  fun _ _ _ ↦ SmoothHCobordant.gluingStatement 𝓘(ℝ, RealModel)

/-- The genuine geometric h-cobordism relation as a classification-layer relation. -/
public noncomputable def geometricHCobordismRelation : SmoothHCobordismRelation where
  setoid :=
    { r := GeometricallyHCobordant
      iseqv :=
        ⟨geometricallyHCobordant_refl,
          fun {_ _} h ↦ geometricallyHCobordant_symm h,
          fun {_ _ _} hXY hYZ ↦ geometricallyHCobordant_trans hXY hYZ⟩ }

@[simp]
public theorem geometricHCobordismRelation_rel
    (X Y : MarkedSmoothSixSphere) :
    geometricHCobordismRelation.setoid.r X Y ↔ X.GeometricallyHCobordant Y :=
  Iff.rfl

end MarkedSmoothSixSphere

end SphereSixComplex
