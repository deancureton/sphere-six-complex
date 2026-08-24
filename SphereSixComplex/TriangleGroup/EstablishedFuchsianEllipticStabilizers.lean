module

public import SphereSixComplex.TriangleGroup.FreeProductCentralizers
public import SphereSixComplex.TriangleGroup.FuchsianOneFixedCommutation
public import SphereSixComplex.TriangleGroup.FuchsianTwoFixedCommutation

/-!
# Established elliptic stabilizers of the explicit Fuchsian triangle group

The two statements below are the stabilizer calculation for the explicit orientation-preserving
`(3, 4, ∞)` triangle group.  Fixing an elliptic point forces matrix commutation with its elliptic
generator, while the reduced-word normal form identifies that generator's centralizer with the
corresponding cyclic free factor.
-/

namespace SphereSixComplex.TriangleGroup

/-- The stabilizer of the order-three elliptic point is exactly the embedded `C₃` factor. -/
public theorem establishedFuchsianOneStabilizerExact (g : Delta) :
    fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint ↔
      ∃ a : CyclicThree, g = Monoid.Coprod.inl a := by
  constructor
  · intro hfixed
    exact eq_inl_of_commute_g₁ g (commute_gOne_of_fuchsianOneFixed g hfixed)
  · rintro ⟨a, rfl⟩
    by_cases ha : a = 1
    · subst a
      simp
    · exact (FreeProductTorsion.fuchsianSourceAction_inl_fixed_iff
        a ha fuchsianOneFixedPoint).2 rfl

/-- The stabilizer of the order-four elliptic point is exactly the embedded `C₄` factor. -/
public theorem establishedFuchsianTwoStabilizerExact (g : Delta) :
    fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint ↔
      ∃ a : CyclicFour, g = Monoid.Coprod.inr a := by
  constructor
  · intro hfixed
    exact eq_inr_of_commute_g₂ g
      (FuchsianTwoFixedCommutation.commute_gTwo_of_fuchsianTwoFixedPoint_fixed g hfixed)
  · rintro ⟨a, rfl⟩
    by_cases ha : a = 1
    · subst a
      simp
    · exact (FreeProductTorsion.fuchsianSourceAction_inr_fixed_iff
        a ha fuchsianTwoFixedPoint).2 rfl

end SphereSixComplex.TriangleGroup
