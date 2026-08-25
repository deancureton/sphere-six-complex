module

public import SphereSixComplex.Topology.OrientedThetaSix
public import SphereSixComplex.Topology.SmoothHCobordism

/-!
# Genuine oriented smooth h-cobordisms of homotopy six-spheres

This module connects the explicit collared-bordism layer to the marked oriented homotopy spheres
used by `Θ₆`.  A witness stores the actual end homotopy equivalences and equalities identifying
their forward maps with the collar inclusions.  Its orientation condition is therefore imposed on
the concrete transition homotopy equivalence from the incoming end to the outgoing end.

Cylinders and reversal are constructed.  The sole missing relation-level operation is composition,
which is factored as the explicit smooth closed-boundary gluing theorem at the end of the file.
-/

@[expose] public section

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

namespace OrientedMarkedSmoothHomotopySixSphere

/-- A genuine oriented smooth h-cobordism between two marked homotopy six-spheres.

The equality fields ensure that the stored homotopy equivalences are carried by the two actual
collar inclusions, rather than merely proving that the three carrier types have the same homotopy
type. -/
public structure SmoothHCobordism
    (D : SixSphereDegreeTheory)
    (X Y : OrientedMarkedSmoothHomotopySixSphere.{0}) where
  /-- The compact smooth seven-dimensional collared bordism. -/
  bordism : SmoothCollaredBordism.{0, 0, 0, 0, 0}
    𝓘(ℝ, RealModel) X.carrier Y.carrier
  /-- Incoming collar inclusion, bundled as a homotopy equivalence. -/
  incomingEquiv : X.carrier ≃ₕ bordism.W
  /-- The incoming equivalence is the specified incoming collar inclusion. -/
  incomingEquiv_toFun :
    (incomingEquiv : X.carrier → bordism.W) = bordism.incoming.inclusion
  /-- Outgoing collar inclusion, bundled as a homotopy equivalence. -/
  outgoingEquiv : Y.carrier ≃ₕ bordism.W
  /-- The outgoing equivalence is the specified outgoing collar inclusion. -/
  outgoingEquiv_toFun :
    (outgoingEquiv : Y.carrier → bordism.W) = bordism.outgoing.inclusion
  /-- The transition from the incoming end to the outgoing end preserves the marked orientation. -/
  orientation_preserving : SameOrientation D X.marking
    ((incomingEquiv.trans outgoingEquiv.symm).trans Y.marking)

namespace SmoothHCobordism

variable {D : SixSphereDegreeTheory}
variable {X Y Z : OrientedMarkedSmoothHomotopySixSphere.{0}}

/-- Forgetting orientation gives the map-level h-cobordism condition on the underlying collared
bordism. -/
public theorem isHCobordism (B : SmoothHCobordism D X Y) : B.bordism.IsHCobordism :=
  ⟨⟨B.incomingEquiv, B.incomingEquiv_toFun⟩,
    ⟨B.outgoingEquiv, B.outgoingEquiv_toFun⟩⟩

/-- The transition homotopy equivalence determined by the two end inclusions. -/
public def transition (B : SmoothHCobordism D X Y) : X.carrier ≃ₕ Y.carrier :=
  B.incomingEquiv.trans B.outgoingEquiv.symm

/-- A version of the standard cylinder whose carrier remains definitionally visible to the
dependent end-equivalence fields below. -/
public abbrev explicitCylinderBordism (X : OrientedMarkedSmoothHomotopySixSphere.{0}) :
    SmoothCollaredBordism.{0, 0, 0, 0, 0}
      𝓘(ℝ, RealModel) X.carrier X.carrier where
  W := X.carrier × CollarParameter
  incoming := SmoothCollaredBordism.cylinderIncomingCollar
  outgoing := SmoothCollaredBordism.cylinderOutgoingCollar
  ends_disjoint := by
    rw [Set.disjoint_left]
    rintro p ⟨x, hx⟩ ⟨y, hy⟩
    rw [SmoothCollaredBordism.cylinderIncomingCollar_inclusion] at hx
    rw [SmoothCollaredBordism.cylinderOutgoingCollar_inclusion] at hy
    have h := congrArg (fun q : X.carrier × CollarParameter ↦ (q.2 : ℝ))
      (hy.trans hx.symm)
    norm_num [collarStart, collarFinish] at h
  boundary_eq := by
    rw [ModelWithCorners.boundary_of_boundaryless_left, boundary_Icc]
    ext p
    rcases p with ⟨x, t⟩
    simp only [Set.mem_union, Set.mem_range,
      SmoothCollaredBordism.cylinderIncomingCollar_inclusion,
      SmoothCollaredBordism.cylinderOutgoingCollar_inclusion]
    change (x ∈ (Set.univ : Set X.carrier) ∧ t ∈ ({⊥, ⊤} : Set CollarParameter)) ↔
      ((∃ y : X.carrier, (y, collarStart) = (x, t)) ∨
        ∃ y : X.carrier, (y, collarFinish) = (x, t))
    simp [collarStart, collarFinish, eq_comm]
    have hzero : (⊥ : CollarParameter) = 0 := Subtype.ext (by norm_num)
    have hone : (⊤ : CollarParameter) = 1 := Subtype.ext (by norm_num)
    simp [hzero, hone]

/-- The cylinder of a marked homotopy six-sphere is an oriented h-cobordism. -/
public def cylinder (D : SixSphereDegreeTheory)
    (X : OrientedMarkedSmoothHomotopySixSphere.{0}) : SmoothHCobordism D X X where
  bordism := explicitCylinderBordism X
  incomingEquiv := cylinderZeroHomotopyEquiv X.carrier
  incomingEquiv_toFun := by
    funext x
    change (x, (0 : Set.Icc (0 : ℝ) 1)) = (x, collarStart)
    exact Prod.ext rfl (Subtype.ext (by norm_num [collarStart]))
  outgoingEquiv := cylinderOneHomotopyEquiv X.carrier
  outgoingEquiv_toFun := by
    funext x
    rw [cylinderOneHomotopyEquiv_toFun]
    rw [SmoothCollaredBordism.cylinderOutgoingCollar_inclusion]
    exact Prod.ext rfl (Subtype.ext (by norm_num [collarFinish]))
  orientation_preserving := by
    apply SameOrientation.of_homotopic
    exact (ContinuousMap.Homotopic.comp (.refl X.marking.toFun) <| by
      convert ContinuousMap.Homotopic.refl (ContinuousMap.id X.carrier) using 1).symm

/-- The same geometric cylinder changes only the chosen marking at its outgoing end, provided the
two markings encode the same orientation. -/
public def cylinderChangeMarking (D : SixSphereDegreeTheory)
    (X : OrientedMarkedSmoothHomotopySixSphere.{0})
    (e : X.carrier ≃ₕ SixSphere) (h : SameOrientation D X.marking e) :
    SmoothHCobordism D X { X with marking := e } where
  bordism := explicitCylinderBordism X
  incomingEquiv := cylinderZeroHomotopyEquiv X.carrier
  incomingEquiv_toFun := by
    funext x
    change (x, (0 : Set.Icc (0 : ℝ) 1)) = (x, collarStart)
    exact Prod.ext rfl (Subtype.ext (by norm_num [collarStart]))
  outgoingEquiv := cylinderOneHomotopyEquiv X.carrier
  outgoingEquiv_toFun := by
    funext x
    rw [cylinderOneHomotopyEquiv_toFun]
    rw [SmoothCollaredBordism.cylinderOutgoingCollar_inclusion]
    exact Prod.ext rfl (Subtype.ext (by norm_num [collarFinish]))
  orientation_preserving := by
    apply SameOrientation.trans D h
    apply SameOrientation.of_homotopic
    exact (ContinuousMap.Homotopic.comp (.refl e.toFun) <| by
      convert ContinuousMap.Homotopic.refl (ContinuousMap.id X.carrier) using 1).symm

/-- Reversing an oriented h-cobordism reverses its two collars and preserves the induced endpoint
orientation condition. -/
public def reverse (B : SmoothHCobordism D X Y) : SmoothHCobordism D Y X where
  bordism := B.bordism.reverse
  incomingEquiv := B.outgoingEquiv
  incomingEquiv_toFun := B.outgoingEquiv_toFun
  outgoingEquiv := B.incomingEquiv
  outgoingEquiv_toFun := B.incomingEquiv_toFun
  orientation_preserving := by
    let t : X.carrier ≃ₕ Y.carrier := B.transition
    have hreverse : SameOrientation D (t.trans Y.marking) X.marking :=
      SameOrientation.symm D B.orientation_preserving
    have hprecomp :
        SameOrientation D (t.symm.trans (t.trans Y.marking))
          (t.symm.trans X.marking) :=
      SameOrientation.precomp D t.symm hreverse
    have hcancel :
        (t.symm.trans (t.trans Y.marking)).toFun.Homotopic Y.marking.toFun :=
      ContinuousMap.Homotopic.comp (.refl Y.marking.toFun) t.right_inv
    exact SameOrientation.trans D
      (SameOrientation.symm D (SameOrientation.of_homotopic D hcancel)) hprecomp

end SmoothHCobordism

/-- Existence of one genuine oriented smooth h-cobordism. -/
public def SmoothHCobordant (D : SixSphereDegreeTheory)
    (X Y : OrientedMarkedSmoothHomotopySixSphere.{0}) : Prop :=
  Nonempty (SmoothHCobordism D X Y)

namespace SmoothHCobordant

variable {D : SixSphereDegreeTheory}
variable {X Y Z : OrientedMarkedSmoothHomotopySixSphere.{0}}

/-- Oriented h-cobordism is reflexive, witnessed by the genuine cylinder. -/
public theorem refl (D : SixSphereDegreeTheory) (X : OrientedMarkedSmoothHomotopySixSphere.{0}) :
    SmoothHCobordant D X X :=
  ⟨SmoothHCobordism.cylinder D X⟩

/-- Oriented h-cobordism is symmetric, witnessed by reversal. -/
public theorem symm (h : SmoothHCobordant D X Y) : SmoothHCobordant D Y X := by
  obtain ⟨B⟩ := h
  exact ⟨B.reverse⟩

/-- The exact smooth closed-boundary gluing theorem needed for transitivity of oriented
h-cobordism.  A witness must include the resulting collars, end equivalences, and orientation
compatibility; this proposition is not assumed anywhere. -/
public def GluingStatement : Prop :=
  ∀ (_B₀₁ : SmoothHCobordism D X Y) (_B₁₂ : SmoothHCobordism D Y Z),
    Nonempty (SmoothHCobordism D X Z)

/-- Smooth oriented gluing implies transitivity. -/
public theorem trans_of_gluing (hglue : GluingStatement (D := D) (X := X) (Y := Y) (Z := Z))
    (h₀₁ : SmoothHCobordant D X Y) (h₁₂ : SmoothHCobordant D Y Z) :
    SmoothHCobordant D X Z := by
  obtain ⟨B₀₁⟩ := h₀₁
  obtain ⟨B₁₂⟩ := h₁₂
  exact hglue B₀₁ B₁₂

end SmoothHCobordant

/-- A global oriented gluing theorem for marked homotopy six-spheres. -/
public def SmoothHCobordismGluingTheorem (D : SixSphereDegreeTheory) : Prop :=
  ∀ X Y Z : OrientedMarkedSmoothHomotopySixSphere.{0},
    SmoothHCobordant.GluingStatement (D := D) (X := X) (Y := Y) (Z := Z)

/-- Once closed-boundary gluing is constructed, genuine oriented h-cobordisms instantiate the
abstract oriented relation used by the `Θ₆` quotient. -/
public def geometricSmoothHCobordismRelation (D : SixSphereDegreeTheory)
    (hglue : SmoothHCobordismGluingTheorem D) : OrientedSmoothHCobordismRelation where
  setoid :=
    { r := SmoothHCobordant D
      iseqv :=
        ⟨SmoothHCobordant.refl D,
          fun {_ _} h ↦ SmoothHCobordant.symm h,
          fun {_ _ _} h₀₁ h₁₂ ↦
            SmoothHCobordant.trans_of_gluing (hglue _ _ _) h₀₁ h₁₂⟩ }

/-- The equivalence relation generated by genuine oriented smooth h-cobordisms.

This is an equally direct presentation of h-cobordism classes which does not require proving the
closed-boundary gluing theorem merely in order to form the quotient.  Every generating edge still
contains an actual collared smooth h-cobordism; reflexivity, reversal, and finite concatenation are
handled by the standard equivalence closure. -/
public def generatedGeometricSmoothHCobordismRelation
    (D : SixSphereDegreeTheory) : OrientedSmoothHCobordismRelation where
  setoid := Relation.EqvGen.setoid (SmoothHCobordant D)

/-- The generated geometric relation forgets the auxiliary choice of marking while retaining its
orientation: the witness is the concrete marking-change cylinder. -/
public theorem generatedGeometricSmoothHCobordismRelation_markingIndependence
    (D : SixSphereDegreeTheory) :
    (generatedGeometricSmoothHCobordismRelation D).MarkingIndependenceObligation D := by
  intro X e h
  exact Relation.EqvGen.rel X { X with marking := e }
    ⟨SmoothHCobordism.cylinderChangeMarking D X e h⟩

/-- In the generated presentation, genuine h-cobordisms from every representative to the
standard sphere immediately prove `Θ₆ = 0`; no smooth gluing theorem or connected-sum structure is
needed. -/
public theorem generatedGeometricThetaSixVanishes_of_hCobordant_standard
    (D : SixSphereDegreeTheory)
    (hStandard : ∀ X : OrientedMarkedSmoothHomotopySixSphere.{0},
      SmoothHCobordant D X OrientedMarkedSmoothHomotopySixSphere.standard) :
    (generatedGeometricSmoothHCobordismRelation D).ThetaSixVanishes := by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  apply Quotient.sound
  exact Relation.EqvGen.trans X OrientedMarkedSmoothHomotopySixSphere.standard Y
    (Relation.EqvGen.rel X OrientedMarkedSmoothHomotopySixSphere.standard (hStandard X))
    (Relation.EqvGen.symm Y OrientedMarkedSmoothHomotopySixSphere.standard
      (Relation.EqvGen.rel Y OrientedMarkedSmoothHomotopySixSphere.standard (hStandard Y)))

/-- The same genuine representative-level input discharges the repository's public compatibility
endpoint through the already-proved oriented-to-compatibility adapter. -/
public theorem generatedGeometricThetaSixVanishesAdapter_of_hCobordant_standard
    (D : SixSphereDegreeTheory)
    (hStandard : ∀ X : OrientedMarkedSmoothHomotopySixSphere.{0},
      SmoothHCobordant D X OrientedMarkedSmoothHomotopySixSphere.standard) :
    (generatedGeometricSmoothHCobordismRelation D).toSmoothHCobordismRelation.ThetaSixVanishes :=
  (generatedGeometricSmoothHCobordismRelation D).thetaSixVanishes_toSmoothHCobordismRelation
    (generatedGeometricThetaSixVanishes_of_hCobordant_standard D hStandard)

/-- The representative-level endpoint of the shortest Kervaire--Milnor proof: if every marked
homotopy six-sphere is genuinely oriented h-cobordant to the standard sphere, then the geometric
oriented quotient `Θ₆` is trivial.

This route needs no connected-sum construction and no group structure on the quotient. -/
public theorem geometricThetaSixVanishes_of_hCobordant_standard
    (D : SixSphereDegreeTheory) (hglue : SmoothHCobordismGluingTheorem D)
    (hStandard : ∀ X : OrientedMarkedSmoothHomotopySixSphere.{0},
      SmoothHCobordant D X OrientedMarkedSmoothHomotopySixSphere.standard) :
    (geometricSmoothHCobordismRelation D hglue).ThetaSixVanishes := by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  apply Quotient.sound
  exact SmoothHCobordant.trans_of_gluing
    (hglue X OrientedMarkedSmoothHomotopySixSphere.standard Y)
    (hStandard X) (SmoothHCobordant.symm (hStandard Y))

end OrientedMarkedSmoothHomotopySixSphere

end SphereSixComplex
