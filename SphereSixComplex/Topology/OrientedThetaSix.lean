module

public import SphereSixComplex.Topology.ConnectedSumQuotient
public import SphereSixComplex.Topology.KervaireMilnorSix
public import SphereSixComplex.Topology.OrientedSmoothHomotopySphere
public import SphereSixComplex.Topology.SmoothSixSphereClassification
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Oriented h-cobordism classes and the `Θ₆` adapter

This file keeps the classical oriented quotient separate from the public recognition layer's
unoriented, topologically marked smooth structures.

No geometric h-cobordism relation or connected sum is fabricated here.  The corresponding
structures are interfaces for values constructed by future boundary/collar/gluing foundations.
What is proved is all quotient bookkeeping, the adapter to
`SmoothHCobordismRelation.ThetaSixVanishes`, and the conditional Kervaire--Milnor reduction.
-/

@[expose] public section

noncomputable section

open ContinuousMap
open scoped ContDiff Manifold

namespace SphereSixComplex

/-- An equivalence relation on oriented, homotopy-marked smooth six-spheres.

For this to be the classical `Θ₆`, `setoid.r` must be instantiated by genuine oriented smooth
h-cobordisms.  This wrapper by itself makes no such claim. -/
public structure OrientedSmoothHCobordismRelation where
  /-- The relation proved reflexive, symmetric, and transitive by geometric bordism operations. -/
  setoid : Setoid OrientedMarkedSmoothHomotopySixSphere

namespace OrientedSmoothHCobordismRelation

/-- Oriented h-cobordism classes, the carrier of the candidate group `Θ₆`. -/
public abbrev Class (H : OrientedSmoothHCobordismRelation) := Quotient H.setoid

/-- Triviality of the concrete oriented quotient. -/
public def ThetaSixVanishes (H : OrientedSmoothHCobordismRelation) : Prop :=
  Subsingleton H.Class

/-- The marking-independence condition needed for the marked presentation to model oriented
homotopy spheres rather than retaining irrelevant choices of homotopy equivalence.  It is stated
relative to the missing degree theory and is not assumed by the quotient bookkeeping. -/
public def MarkingIndependenceObligation (H : OrientedSmoothHCobordismRelation)
    (D : OrientedMarkedSmoothHomotopySixSphere.SixSphereDegreeTheory) : Prop :=
  ∀ (S : OrientedMarkedSmoothHomotopySixSphere)
    (e : S.carrier ≃ₕ SixSphere),
    OrientedMarkedSmoothHomotopySixSphere.SameOrientation D S.marking e →
      H.setoid.r S { S with marking := e }

/-- Connected-sum data linked to the actual standard marked sphere and the explicit orientation
reversal from `OrientedSmoothHomotopySphere`.

Constructing this data geometrically is the named connected-sum obligation left by current
foundations. -/
public structure ConnectedSumData (H : OrientedSmoothHCobordismRelation) where
  /-- Representative-level operation and quotient laws. -/
  quotientData : ConnectedSumQuotientData H.setoid
  /-- Its unit is the actual standard sphere. -/
  standard_eq : quotientData.standard = OrientedMarkedSmoothHomotopySixSphere.standard
  /-- Its inverse operation is the actual antipodal orientation reversal. -/
  reverseOrientation_eq :
    quotientData.reverseOrientation =
      OrientedMarkedSmoothHomotopySixSphere.reverseOrientation

/-- The exact missing connected-sum theorem, stated as a proposition rather than assumed. -/
public def GeometricConnectedSumObligation (H : OrientedSmoothHCobordismRelation) : Prop :=
  Nonempty H.ConnectedSumData

/-- Connected sum makes the oriented h-cobordism quotient an additive commutative group. -/
@[instance_reducible]
public def ConnectedSumData.classAddCommGroup
    {H : OrientedSmoothHCobordismRelation} (D : H.ConnectedSumData) : AddCommGroup H.Class :=
  D.quotientData.addCommGroup

/-- The standard-sphere class is zero for the group induced by connected sum. -/
public theorem ConnectedSumData.standard_class_eq_zero
    {H : OrientedSmoothHCobordismRelation} (D : H.ConnectedSumData) :
    letI : AddCommGroup H.Class := D.classAddCommGroup
    Quotient.mk H.setoid OrientedMarkedSmoothHomotopySixSphere.standard = 0 := by
  let _ : AddCommGroup H.Class := D.classAddCommGroup
  change Quotient.mk H.setoid OrientedMarkedSmoothHomotopySixSphere.standard =
    Quotient.mk H.setoid D.quotientData.standard
  rw [D.standard_eq]

/-- A topologically marked smooth sphere acquires an oriented homotopy marking after choosing its
stored homeomorphism.  This is the only use of choice in the adapter.

The chosen homeomorphism determines one of the two classical orientations; the construction does
not identify the oriented and unoriented quotients. -/
public noncomputable def orientCompatibilityObject
    (X : MarkedSmoothSixSphere) : OrientedMarkedSmoothHomotopySixSphere := by
  let e : X.Carrier ≃ₜ SixSphere := Classical.choice X.homeomorph
  letI : ConnectedSpace SixSphere := sixSphere_connectedSpace
  exact
    { carrier := X.Carrier
      topologicalSpace := inferInstance
      chartedSpace := inferInstance
      t2Space := e.symm.t2Space
      secondCountableTopology := e.secondCountableTopology
      isManifold := inferInstance
      compactSpace := e.symm.compactSpace
      connectedSpace := connectedSpace_of_homeomorph e.symm
      boundaryless := inferInstance
      marking := e.toHomotopyEquiv }

/-- Pull an oriented relation back along the choice of orientation on compatibility objects.

This supplies the repository's existing interface without asserting that its class type is
definitionally the classical oriented group. -/
public noncomputable def toSmoothHCobordismRelation
    (H : OrientedSmoothHCobordismRelation) : SmoothHCobordismRelation where
  setoid := H.setoid.comap orientCompatibilityObject

/-- Map compatibility classes to the concrete oriented quotient. -/
public noncomputable def compatibilityClassToOrientedClass
    (H : OrientedSmoothHCobordismRelation) :
    H.toSmoothHCobordismRelation.Class → H.Class :=
  Quotient.map orientCompatibilityObject fun _ _ h ↦ h

@[simp]
public theorem compatibilityClassToOrientedClass_mk
    (H : OrientedSmoothHCobordismRelation) (X : MarkedSmoothSixSphere) :
    H.compatibilityClassToOrientedClass
      (Quotient.mk H.toSmoothHCobordismRelation.setoid X) =
      Quotient.mk H.setoid (orientCompatibilityObject X) :=
  rfl

/-- Adapter from triviality of the genuine oriented quotient to the repository compatibility
endpoint `SmoothHCobordismRelation.ThetaSixVanishes`. -/
public theorem thetaSixVanishes_toSmoothHCobordismRelation
    (H : OrientedSmoothHCobordismRelation) (hTheta : H.ThetaSixVanishes) :
    H.toSmoothHCobordismRelation.ThetaSixVanishes := by
  constructor
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro X Y
  apply Quotient.sound
  have hOriented :
      H.setoid.r (orientCompatibilityObject X) (orientCompatibilityObject Y) := by
    apply Quotient.exact
    exact @Subsingleton.elim H.Class hTheta
      (Quotient.mk H.setoid (orientCompatibilityObject X))
      (Quotient.mk H.setoid (orientCompatibilityObject Y))
  exact hOriented

/-- The oriented h-cobordism theorem as a separate proposition.  It is not used in the computation
of `Θ₆`; it is used only afterward to obtain diffeomorphisms. -/
public def HCobordismTheoremSix (H : OrientedSmoothHCobordismRelation) : Prop :=
  ∀ {X Y : OrientedMarkedSmoothHomotopySixSphere}, H.setoid.r X Y →
    Nonempty
      (Diffeomorph 𝓘(ℝ, RealModel) 𝓘(ℝ, RealModel) X.carrier Y.carrier ∞)

/-- The oriented h-cobordism theorem transports to the public compatibility relation. -/
public theorem hCobordismTheoremSix_toSmoothHCobordismRelation
    (H : OrientedSmoothHCobordismRelation) (h : H.HCobordismTheoremSix) :
    H.toSmoothHCobordismRelation.HCobordismTheoremSix := by
  intro X Y hXY
  exact h hXY

/-- The Kervaire--Milnor exact-sequence argument discharges the concrete `Θ₆` endpoint once
the quotient already carries its connected-sum group structure. -/
public theorem thetaSixVanishes_of_kervaireMilnor
    (H : OrientedSmoothHCobordismRelation) [AddCommGroup H.Class]
    (S : KervaireMilnorSixSequence H.Class) (h : S.DimensionSixComputations) :
    H.ThetaSixVanishes :=
  S.theta_subsingleton_of_dimensionSixComputations h

/-- Minimal form of the Kervaire--Milnor computation: exactness at the oriented homotopy-sphere
group, `bP₇ = 0`, injectivity of the degree-six Kervaire invariant, and its geometric vanishing
already imply `Θ₆ = 0`.  No chosen stable-stem isomorphism and no exactness at the framed term
are used by this proof. -/
public theorem thetaSixVanishes_of_minimalKervaireMilnor
    (H : OrientedSmoothHCobordismRelation) [AddCommGroup H.Class]
    (S : KervaireMilnorSixSequence H.Class)
    (hBP : S.ParallelizableBoundarySevenVanishes)
    (hInjective : S.KervaireInvariantInjective)
    (hVanishes : S.KervaireInvariantVanishesOnHomotopySpheres) :
    H.ThetaSixVanishes :=
  S.theta_subsingleton_of_kervaire hBP hInjective hVanishes

/-- Structure-free minimal adapter: only the maps and exactness actually used by the
Kervaire--Milnor argument are required. -/
public theorem thetaSixVanishes_of_minimalKervaireData
    (H : OrientedSmoothHCobordismRelation) [AddCommGroup H.Class]
    {BP Framed : Type*} [AddCommGroup BP] [AddCommGroup Framed]
    (parallelizableBoundary : BP →+ H.Class)
    (stableFramingClass : H.Class →+ Framed)
    (kervaireInvariant : Framed →+ ZMod 2)
    (hexact : Function.Exact parallelizableBoundary stableFramingClass)
    (hBP : Subsingleton BP) (hInjective : Function.Injective kervaireInvariant)
    (hVanishes : ∀ x : H.Class, kervaireInvariant (stableFramingClass x) = 0) :
    H.ThetaSixVanishes :=
  theta_subsingleton_of_minimal_kervaire_data parallelizableBoundary stableFramingClass
    kervaireInvariant hexact hBP hInjective hVanishes

/-- Strongest current end-to-end reduction: geometric connected sum supplies the group, the
Kervaire--Milnor exact segment and its two computations kill it, and the proved adapter discharges
the repository's `SmoothHCobordismRelation.ThetaSixVanishes` interface. -/
public theorem thetaSixVanishesAdapter_of_connectedSum_kervaireMilnor
    (H : OrientedSmoothHCobordismRelation) (D : H.ConnectedSumData) :
    letI : AddCommGroup H.Class := D.classAddCommGroup
    ∀ (S : KervaireMilnorSixSequence H.Class), S.DimensionSixComputations →
      H.toSmoothHCobordismRelation.ThetaSixVanishes := by
  let _ : AddCommGroup H.Class := D.classAddCommGroup
  intro S h
  exact H.thetaSixVanishes_toSmoothHCobordismRelation
    (H.thetaSixVanishes_of_kervaireMilnor S h)

end OrientedSmoothHCobordismRelation

end SphereSixComplex
