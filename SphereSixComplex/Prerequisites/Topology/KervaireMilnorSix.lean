module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# The algebraic core of the dimension-six Kervaire--Milnor computation

This file formalizes the exact-sequence argument after the geometric terms and maps have been
constructed.  It does **not** postulate those constructions.  Instead, `KervaireMilnorSixSequence`
is data to be supplied by future framed-bordism and surgery foundations, and each classical
calculation is exposed as a named proposition.

For an additive group `Theta`, the relevant portion is

```
    bP₇ ⟶ Theta ⟶ (framed bordism in degree 6)/(image J) ⟶ Z/2.
```

Exactness, `bP₇ = 0`, the stable-six-stem computation, and identification of the Kervaire
invariant imply that `Theta` is trivial.  The proof below is elementary algebra and is checked by
Lean.
-/

@[expose] public section

namespace SphereSixComplex

/-- The genuinely minimal algebraic Kervaire--Milnor reduction, stated without a structure that
also demands unused exactness at the framed-bordism term.  Exactness at `Theta`, triviality of the
parallelizable-boundary source, injectivity of Kervaire, and pointwise Kervaire vanishing force an
individual class to vanish. -/
public theorem thetaElement_eq_zero_of_minimal_kervaire_data
    {BP Theta Framed : Type*} [AddCommGroup BP] [AddCommGroup Theta]
    [AddCommGroup Framed]
    (parallelizableBoundary : BP →+ Theta)
    (stableFramingClass : Theta →+ Framed)
    (kervaireInvariant : Framed →+ ZMod 2)
    (hexact : Function.Exact parallelizableBoundary stableFramingClass)
    (hBP : Subsingleton BP) (hInjective : Function.Injective kervaireInvariant)
    (hVanishes : ∀ x : Theta, kervaireInvariant (stableFramingClass x) = 0)
    (x : Theta) : x = 0 := by
  let _ : Subsingleton BP := hBP
  have hStableFraming : stableFramingClass x = 0 := by
    apply hInjective
    rw [map_zero]
    exact hVanishes x
  obtain ⟨b, hb⟩ := (hexact x).mp hStableFraming
  calc
    x = parallelizableBoundary b := hb.symm
    _ = parallelizableBoundary 0 := congrArg parallelizableBoundary (Subsingleton.elim b 0)
    _ = 0 := map_zero parallelizableBoundary

/-- The minimal data above make the whole candidate group of homotopy spheres a subsingleton. -/
public theorem theta_subsingleton_of_minimal_kervaire_data
    {BP Theta Framed : Type*} [AddCommGroup BP] [AddCommGroup Theta]
    [AddCommGroup Framed]
    (parallelizableBoundary : BP →+ Theta)
    (stableFramingClass : Theta →+ Framed)
    (kervaireInvariant : Framed →+ ZMod 2)
    (hexact : Function.Exact parallelizableBoundary stableFramingClass)
    (hBP : Subsingleton BP) (hInjective : Function.Injective kervaireInvariant)
    (hVanishes : ∀ x : Theta, kervaireInvariant (stableFramingClass x) = 0) :
    Subsingleton Theta where
  allEq x y := by
    apply sub_eq_zero.mp
    exact thetaElement_eq_zero_of_minimal_kervaire_data
      parallelizableBoundary stableFramingClass kervaireInvariant hexact hBP hInjective
        hVanishes (x - y)

/-- The degree-six portion of the Kervaire--Milnor exact sequence.

The names describe the intended geometric interpretation, while the fields state only honest
algebraic exactness.  Constructing a value of this structure for h-cobordism classes is a missing
standard theorem, not a structure field restating `Theta = 0`. -/
public structure KervaireMilnorSixSequence.{u} (Theta : Type u) [AddCommGroup Theta] where
  /-- Homotopy six-spheres bounding parallelizable seven-manifolds. -/
  bPSeven : Type u
  /-- The group structure on `bP₇`. -/
  [bPSevenGroup : AddCommGroup bPSeven]
  /-- Degree-six framed bordism modulo the stable `J`-image. -/
  framedBordismModuloJ : Type u
  /-- Its additive group structure. -/
  [framedBordismModuloJGroup : AddCommGroup framedBordismModuloJ]
  /-- Inclusion of parallelizable-boundary spheres. -/
  parallelizableBoundary : bPSeven →+ Theta
  /-- Stable framing (normal invariant) of a homotopy sphere. -/
  stableFramingClass : Theta →+ framedBordismModuloJ
  /-- The Kervaire invariant in degree six. -/
  kervaireInvariant : framedBordismModuloJ →+ ZMod 2
  /-- Exactness at the group of homotopy spheres. -/
  exactAtTheta : Function.Exact parallelizableBoundary stableFramingClass
  /-- Exactness at framed bordism modulo `J`. -/
  exactAtFramedBordism : Function.Exact stableFramingClass kervaireInvariant

namespace KervaireMilnorSixSequence

instance {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta) :
    AddCommGroup S.bPSeven :=
  S.bPSevenGroup

instance {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta) :
    AddCommGroup S.framedBordismModuloJ :=
  S.framedBordismModuloJGroup

/-- The classical calculation `bP₇ = 0`, isolated from exactness. -/
public def ParallelizableBoundarySevenVanishes
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta) : Prop :=
  Subsingleton S.bPSeven

/-- The stable calculation that framed bordism modulo `J` in degree six is cyclic of order two. -/
public def StableSixStemModuloJIsZModTwo
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta) : Prop :=
  Nonempty (S.framedBordismModuloJ ≃+ ZMod 2)

/-- Identification of the geometric Kervaire invariant with a selected stable-stem computation.

Keeping this separate from `StableSixStemModuloJIsZModTwo` prevents the mere abstract group
isomorphism with `Z/2` from silently doing the work of detecting its nonzero element. -/
public def KervaireInvariantMatches
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta)
    (stableStemComputation : S.framedBordismModuloJ ≃+ ZMod 2) : Prop :=
  ∀ x, S.kervaireInvariant x = stableStemComputation x

/-- The Kervaire invariant detects every degree-six framed-bordism class modulo `J`.

For the vanishing of `Θ₆`, injectivity is the exact stable-stem input needed; choosing an
explicit isomorphism with `ZMod 2` is stronger than necessary. -/
public def KervaireInvariantInjective
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta) : Prop :=
  Function.Injective S.kervaireInvariant

/-- The Kervaire invariant vanishes on the stable framing class of every homotopy sphere.

Geometrically this follows because the defining quadratic form is carried by
`H₃(Σ; 𝔽₂)`, which is zero for a homotopy six-sphere. -/
public def KervaireInvariantVanishesOnHomotopySpheres
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta) : Prop :=
  ∀ x : Theta, S.kervaireInvariant (S.stableFramingClass x) = 0

/-- Exactness at `Theta`, vanishing of `bP₇`, injectivity of the Kervaire invariant, and its
vanishing on homotopy spheres kill an individual element.

This is the minimal algebraic form of the representative-level Kervaire--Milnor proof.  It does
not use exactness at framed bordism and does not choose an isomorphism of the stable stem with
`ZMod 2`. -/
public theorem thetaElement_eq_zero_of_kervaire
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta)
    (hBP : S.ParallelizableBoundarySevenVanishes)
    (hInjective : S.KervaireInvariantInjective)
    (hVanishes : S.KervaireInvariantVanishesOnHomotopySpheres)
    (x : Theta) : x = 0 := by
  let _ : Subsingleton S.bPSeven := hBP
  have hStableFraming : S.stableFramingClass x = 0 := by
    apply hInjective
    rw [map_zero]
    exact hVanishes x
  obtain ⟨b, hb⟩ := (S.exactAtTheta x).mp hStableFraming
  calc
    x = S.parallelizableBoundary b := hb.symm
    _ = S.parallelizableBoundary 0 := congrArg S.parallelizableBoundary (Subsingleton.elim b 0)
    _ = 0 := map_zero S.parallelizableBoundary

/-- Minimal Kervaire--Milnor reduction for the whole candidate group. -/
public theorem theta_subsingleton_of_kervaire
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta)
    (hBP : S.ParallelizableBoundarySevenVanishes)
    (hInjective : S.KervaireInvariantInjective)
    (hVanishes : S.KervaireInvariantVanishesOnHomotopySpheres) :
    Subsingleton Theta where
  allEq x y := by
    apply sub_eq_zero.mp
    exact S.thetaElement_eq_zero_of_kervaire hBP hInjective hVanishes (x - y)

/-- Exactness plus the two dimension-six computations kills every element of `Theta`. -/
public theorem thetaElement_eq_zero
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta)
    (hBP : S.ParallelizableBoundarySevenVanishes)
    (stableStemComputation : S.framedBordismModuloJ ≃+ ZMod 2)
    (hKervaire : S.KervaireInvariantMatches stableStemComputation)
    (x : Theta) : x = 0 := by
  let _ : Subsingleton S.bPSeven := hBP
  have hKervaireInjective : Function.Injective S.kervaireInvariant := by
    intro a b hab
    apply stableStemComputation.injective
    rw [← hKervaire a, ← hKervaire b, hab]
  have hStableFraming : S.stableFramingClass x = 0 := by
    apply hKervaireInjective
    rw [map_zero]
    exact S.exactAtFramedBordism.apply_apply_eq_zero x
  obtain ⟨b, hb⟩ := (S.exactAtTheta x).mp hStableFraming
  calc
    x = S.parallelizableBoundary b := hb.symm
    _ = S.parallelizableBoundary 0 := congrArg S.parallelizableBoundary (Subsingleton.elim b 0)
    _ = 0 := map_zero S.parallelizableBoundary

/-- The full conditional Kervaire--Milnor reduction: the candidate group of homotopy six-spheres
is a subsingleton. -/
public theorem theta_subsingleton
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta)
    (hBP : S.ParallelizableBoundarySevenVanishes)
    (stableStemComputation : S.framedBordismModuloJ ≃+ ZMod 2)
    (hKervaire : S.KervaireInvariantMatches stableStemComputation) :
    Subsingleton Theta where
  allEq x y := by
    apply sub_eq_zero.mp
    exact S.thetaElement_eq_zero hBP stableStemComputation hKervaire (x - y)

/-- A bundled name for the two genuinely computational inputs, useful for downstream adapters. -/
public def DimensionSixComputations
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta) : Prop :=
  S.ParallelizableBoundarySevenVanishes ∧
    ∃ e : S.framedBordismModuloJ ≃+ ZMod 2, S.KervaireInvariantMatches e

/-- Bundling the computations does not change the reduction. -/
public theorem theta_subsingleton_of_dimensionSixComputations
    {Theta : Type*} [AddCommGroup Theta] (S : KervaireMilnorSixSequence Theta)
    (h : S.DimensionSixComputations) : Subsingleton Theta := by
  obtain ⟨hBP, e, he⟩ := h
  exact S.theta_subsingleton hBP e he

end KervaireMilnorSixSequence

end SphereSixComplex
