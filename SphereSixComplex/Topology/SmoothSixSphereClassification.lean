module

public import SphereSixComplex.Topology.SmoothRecognitionFoundations

/-!
# Factoring smooth six-sphere classification

This compatibility layer separates three statements which must not be conflated:

* generalized topological Poincare in dimension six;
* triviality of a chosen h-cobordism quotient;
* the h-cobordism theorem, which turns the chosen geometric relation into diffeomorphism.

`MarkedSmoothSixSphere` below is intentionally the existing *unoriented* recognition object: a
smooth structure on a type topologically marked as `S⁶`.  The classical oriented group `Θ₆` is a
different construction.  A later module supplies an explicit adapter from an oriented quotient to
this public recognition interface.
-/

@[expose] public section

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- Generalized topological Poincare in dimension six, with the classical manifold hypotheses
made explicit. -/
public def GeneralizedTopologicalPoincareSix : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M],
    Nonempty (M ≃ₕ SixSphere) → Nonempty (M ≃ₜ SixSphere)

/-- The standard-model smooth Poincare statement used by the recognition layer. -/
public def SmoothPoincareSixStandardModel : Prop :=
  ∀ (M : Type) [TopologicalSpace M] [ChartedSpace RealModel M]
    [IsManifold 𝓘(ℝ, RealModel) ∞ M] [T2Space M] [SecondCountableTopology M]
    [CompactSpace M],
    Nonempty (M ≃ₕ SixSphere) → SmoothDiffeomorphicToSixSphere M

/-- An unoriented smooth structure on a carrier topologically marked as the standard six-sphere.

This is the public compatibility object used for smooth recognition, not an element of the
classical oriented group `Θ₆`. -/
public structure MarkedSmoothSixSphere where
  /-- The underlying carrier. -/
  Carrier : Type
  /-- Its topology. -/
  [topology : TopologicalSpace Carrier]
  /-- Its smooth six-dimensional atlas. -/
  [chartedSpace : ChartedSpace RealModel Carrier]
  /-- Smoothness of the atlas. -/
  [isManifold : IsManifold 𝓘(ℝ, RealModel) ∞ Carrier]
  /-- A topological marking by the standard sphere. -/
  homeomorph : Nonempty (Carrier ≃ₜ SixSphere)

namespace MarkedSmoothSixSphere

public instance (X : MarkedSmoothSixSphere) : TopologicalSpace X.Carrier := X.topology
public instance (X : MarkedSmoothSixSphere) : ChartedSpace RealModel X.Carrier := X.chartedSpace
public instance (X : MarkedSmoothSixSphere) : IsManifold 𝓘(ℝ, RealModel) ∞ X.Carrier :=
  X.isManifold

/-- Smooth diffeomorphism of marked-sphere carriers.  The topological markings are deliberately
not required to commute: this is the unoriented recognition quotient. -/
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

/-- Diffeomorphism as an equivalence relation. -/
public def diffeomorphismSetoid : Setoid MarkedSmoothSixSphere where
  r := Diffeomorphic
  iseqv := ⟨diffeomorphic_refl, fun {_ _} h ↦ diffeomorphic_symm h,
    fun {_ _ _} hXY hYZ ↦ diffeomorphic_trans hXY hYZ⟩

public abbrev DiffeomorphismClass := Quotient diffeomorphismSetoid

public def classOf (X : MarkedSmoothSixSphere) : DiffeomorphismClass :=
  Quotient.mk diffeomorphismSetoid X

/-- The standard topologically marked sphere. -/
public noncomputable def standard : MarkedSmoothSixSphere where
  Carrier := SixSphere
  topology := inferInstance
  chartedSpace := inferInstance
  isManifold := inferInstance
  homeomorph := ⟨Homeomorph.refl SixSphere⟩

/-- There is only one unoriented diffeomorphism class of marked smooth six-spheres. -/
public def DiffeomorphismClassesTrivial : Prop := Subsingleton DiffeomorphismClass

public theorem diffeomorphic_standard_of_classes_trivial
    (h : DiffeomorphismClassesTrivial) (X : MarkedSmoothSixSphere) :
    X.Diffeomorphic standard := by
  change diffeomorphismSetoid.r X standard
  apply Quotient.exact
  exact @Subsingleton.elim DiffeomorphismClass h (classOf X) (classOf standard)

end MarkedSmoothSixSphere

/-- Abstract interface for a genuine smooth oriented h-cobordism relation supplied by a geometric
module.  Merely constructing this setoid does not prove that it is geometric. -/
public structure SmoothHCobordismRelation where
  /-- The equivalence relation represented by oriented h-cobordisms. -/
  setoid : Setoid MarkedSmoothSixSphere

namespace SmoothHCobordismRelation

/-- Classes for the supplied relation.  For a genuine oriented relation, a separate adapter must
justify why this quotient represents the oriented group `Θ₆`. -/
public abbrev Class (H : SmoothHCobordismRelation) := Quotient H.setoid

/-- The h-cobordism theorem specialized to the relation supplied by `H`. -/
public def HCobordismTheoremSix (H : SmoothHCobordismRelation) : Prop :=
  ∀ {X Y : MarkedSmoothSixSphere}, H.setoid.r X Y → X.Diffeomorphic Y

/-- The quotient underlying the supplied h-cobordism relation is trivial.

This name is a compatibility endpoint.  It denotes the classical assertion `Θ₆ = 0` only after
the relation has been connected to oriented homotopy spheres and geometric h-cobordisms. -/
public def ThetaSixVanishes (H : SmoothHCobordismRelation) : Prop :=
  Subsingleton H.Class

/-- Triviality of the h-cobordism quotient and the h-cobordism theorem together imply triviality
of the unoriented diffeomorphism quotient. -/
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

/-- Triviality of the marked diffeomorphism quotient discharges the no-exotic-smoothing
obligation for a fixed carrier. -/
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

/-- Topological Poincare followed by uniqueness of the smooth structure gives smooth Poincare in
the standard model. -/
public theorem smoothPoincareSixStandardModel_of_classicalStages
    (hSmale : GeneralizedTopologicalPoincareSix)
    (hClasses : MarkedSmoothSixSphere.DiffeomorphismClassesTrivial) :
    SmoothPoincareSixStandardModel := by
  intro M _ _ _ _ _ _ hHomotopy
  exact homeomorphismToDiffeomorphismSixSphere_of_classes_trivial hClasses
    inferInstance (hSmale M hHomotopy)

/-- The three logically separate classical inputs give the fixed-carrier smooth recognition step. -/
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
