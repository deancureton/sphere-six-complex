module

public import SphereSixComplex.Topology.KervaireMilnorSix
public import SphereSixComplex.Topology.HomotopySphereHomology
public import SphereSixComplex.Topology.FramedBordismSixReduction
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Module.MinimalAxioms
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The geometric Kervaire invariant of a framed homotopy six-sphere

For a stably framed `6`-manifold the geometric Kervaire invariant is the Arf invariant of a
quadratic refinement on middle-dimensional mod-two homology.  Mathlib does not yet contain Arf
invariants, framed bordism, or Pontryagin--Thom theory.  This file nevertheless formalizes the
part of the argument which only uses the defining symplectic-basis formula.

The key point is elementary but useful: if `H₃(-; 𝔽₂)` is zero, every term in the Arf sum
is zero.  The remaining proposition `StableFramedSixSphereKervairePTDetection` asks for precisely
the unavailable geometric construction and detection theorem: a stable framing supplies its
middle-homology quadratic datum, and vanishing of the resulting invariant supplies a genuine
parallelizable seven-dimensional filling.

Thus the final adapter is strictly more informative than simply assuming that all stable
framings bound: it factors that assertion through an explicit, independently computed invariant.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

/-- A quadratic refinement over `𝔽₂`, together with a finite symplectic basis.

The displayed basis identities say that the polar form has the standard hyperbolic matrix.  In
particular this is the usual input on which the Arf invariant is computed. -/
public structure ModTwoSymplecticQuadraticDatum
    (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] where
  /-- Half the dimension of the symplectic vector space. -/
  genus : ℕ
  /-- A symplectic basis, ordered as the two halves of a hyperbolic basis. -/
  symplecticBasis : Module.Basis (Fin genus ⊕ Fin genus) (ZMod 2) V
  /-- The quadratic refinement whose Arf invariant is to be taken. -/
  quadraticRefinement : QuadraticForm (ZMod 2) V
  /-- The first half of the basis is isotropic for the polar form. -/
  polar_inl (i j : Fin genus) :
    quadraticRefinement.polarBilin
      (symplecticBasis (Sum.inl i)) (symplecticBasis (Sum.inl j)) = 0
  /-- The second half of the basis is isotropic for the polar form. -/
  polar_inr (i j : Fin genus) :
    quadraticRefinement.polarBilin
      (symplecticBasis (Sum.inr i)) (symplecticBasis (Sum.inr j)) = 0
  /-- The two halves pair by the identity matrix. -/
  polar_cross (i j : Fin genus) :
    quadraticRefinement.polarBilin
      (symplecticBasis (Sum.inl i)) (symplecticBasis (Sum.inr j)) =
        if i = j then 1 else 0

namespace ModTwoSymplecticQuadraticDatum

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The Arf invariant in a chosen symplectic basis:
`∑ i, q(eᵢ)q(fᵢ) ∈ 𝔽₂`.

The symplectic identities in `ModTwoSymplecticQuadraticDatum` are exactly what makes this the
classical Arf formula rather than an arbitrary sum attached to an arbitrary basis. -/
public def arfInvariant (D : ModTwoSymplecticQuadraticDatum V) : ZMod 2 :=
  ∑ i : Fin D.genus,
    D.quadraticRefinement (D.symplecticBasis (Sum.inl i)) *
      D.quadraticRefinement (D.symplecticBasis (Sum.inr i))

/-- The Arf invariant of a quadratic datum on the zero vector space vanishes. -/
public theorem arfInvariant_eq_zero_of_subsingleton
    (D : ModTwoSymplecticQuadraticDatum V) [Subsingleton V] :
    D.arfInvariant = 0 := by
  simp only [arfInvariant, Subsingleton.elim (D.symplecticBasis (Sum.inl _)) 0,
    Subsingleton.elim (D.symplecticBasis (Sum.inr _)) 0, QuadraticMap.map_zero, zero_mul,
    Finset.sum_const_zero]

end ModTwoSymplecticQuadraticDatum

namespace OrientedMarkedSmoothHomotopySixSphere

/-- The underlying abelian group of middle-dimensional mod-two singular homology. -/
public abbrev ModTwoMiddleHomology
    (S : OrientedMarkedSmoothHomotopySixSphere.{0}) : Type :=
  (((singularHomologyFunctor AddCommGrpCat 3).obj
    (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of S.carrier) : AddCommGrpCat)

/-- A middle-homology quadratic datum for a particular stable framing.

The stable framing is an index of the structure because the quadratic refinement depends on that
framing.  The module structure is stored explicitly: the singular-homology functor currently
lands in `AddCommGrpCat`, so its natural `𝔽₂`-linear structure is not retained in the categorical
codomain. -/
public structure StableFramingKervaireDatum
    (S : OrientedMarkedSmoothHomotopySixSphere.{0})
    (_f : SmoothStableFramingSix (M := S.carrier)) where
  /-- The mod-two scalar action on middle homology. -/
  moduleStructure : Module (ZMod 2) S.ModTwoMiddleHomology
  /-- The framed quadratic refinement and its symplectic basis. -/
  quadraticDatum :
    @ModTwoSymplecticQuadraticDatum S.ModTwoMiddleHomology
      inferInstance moduleStructure

namespace StableFramingKervaireDatum

variable {S : OrientedMarkedSmoothHomotopySixSphere.{0}}
  {f : SmoothStableFramingSix (M := S.carrier)}

/-- The geometric Kervaire invariant, expressed as the Arf invariant of the framed quadratic
refinement on `H₃(S; 𝔽₂)`. -/
public def kervaireInvariant (D : StableFramingKervaireDatum S f) : ZMod 2 := by
  letI : Module (ZMod 2) S.ModTwoMiddleHomology := D.moduleStructure
  exact D.quadraticDatum.arfInvariant

/-- A zero middle-homology object forces the Kervaire invariant of every stable framing datum to
vanish. -/
public theorem kervaireInvariant_eq_zero_of_middleHomology_isZero
    (D : StableFramingKervaireDatum S f)
    (hH₃ : IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of S.carrier))) :
    D.kervaireInvariant = 0 := by
  letI : Module (ZMod 2) S.ModTwoMiddleHomology := D.moduleStructure
  letI : Subsingleton S.ModTwoMiddleHomology :=
    AddCommGrpCat.subsingleton_of_isZero hH₃
  exact D.quadraticDatum.arfInvariant_eq_zero_of_subsingleton

/-- When middle homology is zero, its framed quadratic datum can be constructed explicitly: it
has genus zero, the empty symplectic basis, and the zero quadratic form.

No geometric choice remains in this case.  The scalar action, basis, and quadratic refinement on
a zero abelian group are all unique. -/
public def ofMiddleHomologyIsZero
    (S : OrientedMarkedSmoothHomotopySixSphere.{0})
    (f : SmoothStableFramingSix (M := S.carrier))
    (hH₃ : IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of S.carrier))) :
    StableFramingKervaireDatum S f := by
  letI : Subsingleton S.ModTwoMiddleHomology :=
    AddCommGrpCat.subsingleton_of_isZero hH₃
  letI : SMul (ZMod 2) S.ModTwoMiddleHomology := ⟨fun _ _ ↦ 0⟩
  let moduleStructure : Module (ZMod 2) S.ModTwoMiddleHomology :=
    Module.ofMinimalAxioms
      (fun _ _ _ ↦ Subsingleton.elim _ _)
      (fun _ _ _ ↦ Subsingleton.elim _ _)
      (fun _ _ _ ↦ Subsingleton.elim _ _)
      (fun _ ↦ Subsingleton.elim _ _)
  letI : Module (ZMod 2) S.ModTwoMiddleHomology := moduleStructure
  exact
    { moduleStructure := moduleStructure
      quadraticDatum :=
        { genus := 0
          symplecticBasis := Module.Basis.empty S.ModTwoMiddleHomology
          quadraticRefinement := 0
          polar_inl := fun i ↦ Fin.elim0 i
          polar_inr := fun i ↦ Fin.elim0 i
          polar_cross := fun i ↦ Fin.elim0 i } }

end StableFramingKervaireDatum

/-- The single missing geometric/stable-homotopy theorem needed after the algebraic Arf
calculation.

It is the presently unavailable stable-stem/Pontryagin--Thom detection statement:

* the supplied datum is understood as the middle-homology quadratic refinement of the indexed
  stable framing;
* the dimension-six calculation detects framed null-bordism when its Arf invariant is zero and
  produces an actual parallelizable seven-dimensional filling.

The conclusion is a genuine `SmoothParallelizableFillingSix`, not an abstract bordism class and
not a restatement that `Θ₆` vanishes. -/
public def StableFramedSixSphereKervairePTDetection : Prop :=
  ∀ (S : OrientedMarkedSmoothHomotopySixSphere.{0})
    (f : SmoothStableFramingSix (M := S.carrier))
    (D : StableFramingKervaireDatum S f),
    D.kervaireInvariant = 0 → Nonempty (SmoothParallelizableFillingSix S)

/-- The Kervaire detection theorem and vanishing of middle mod-two homology give a genuine
parallelizable filling for a specified stably framed homotopy six-sphere. -/
public theorem parallelizableFilling_of_kervaireDetection
    (hDetection : StableFramedSixSphereKervairePTDetection)
    (S : OrientedMarkedSmoothHomotopySixSphere.{0})
    (f : SmoothStableFramingSix (M := S.carrier))
    (hH₃ : IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
      (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of S.carrier))) :
    Nonempty (SmoothParallelizableFillingSix S) := by
  let D := StableFramingKervaireDatum.ofMiddleHomologyIsZero S f hH₃
  exact hDetection S f D
    (D.kervaireInvariant_eq_zero_of_middleHomology_isZero hH₃)

/-- Uniform middle-homology vanishing plus the one Kervaire/Pontryagin--Thom detection theorem
discharges the older, stronger-looking parallelizable-filling obligation. -/
public theorem stableFramingsBoundParallelizableSevenManifolds_of_kervaireDetection
    (hH₃ : ∀ S : OrientedMarkedSmoothHomotopySixSphere.{0},
      IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
        (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of S.carrier)))
    (hDetection : StableFramedSixSphereKervairePTDetection) :
    StableFramingsBoundParallelizableSevenManifolds := by
  intro S f
  exact parallelizableFilling_of_kervaireDetection hDetection S f (hH₃ S)

/-- It is enough to calculate `H₃(S⁶; 𝔽₂) = 0` for the standard sphere: the marking transports
that calculation to every representative, after which Kervaire detection supplies the filling. -/
public theorem stableFramingsBoundParallelizableSevenManifolds_of_standard_modTwoH₃
    (hstandard :
      IsZero (((singularHomologyFunctor AddCommGrpCat 3).obj
        (AddCommGrpCat.of (ZMod 2))).obj (TopCat.of SixSphere)))
    (hDetection : StableFramedSixSphereKervairePTDetection) :
    StableFramingsBoundParallelizableSevenManifolds :=
  stableFramingsBoundParallelizableSevenManifolds_of_kervaireDetection
    (markedHomotopySixSphere_modTwoHomology_three_isZero_of_standard hstandard) hDetection

end OrientedMarkedSmoothHomotopySixSphere

end SphereSixComplex
