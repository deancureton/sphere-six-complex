module

public import SphereSixComplex.TriangleGroup.FreeProductTorsion

/-!
# Established elliptic stabilizers of the explicit Fuchsian triangle group

The two statements below are the classical stabilizer calculation for the explicit
orientation-preserving `(3, 4, ∞)` triangle group. They are independent of the period family and
the six-sphere construction.
-/

namespace SphereSixComplex.TriangleGroup

/-- The stabilizer of the order-three elliptic point is exactly the embedded `C₃` factor. -/
public axiom establishedFuchsianOneStabilizerExact (g : Delta) :
    fuchsianSourceAction g • fuchsianOneFixedPoint = fuchsianOneFixedPoint ↔
      ∃ a : CyclicThree, g = Monoid.Coprod.inl a

/-- The stabilizer of the order-four elliptic point is exactly the embedded `C₄` factor. -/
public axiom establishedFuchsianTwoStabilizerExact (g : Delta) :
    fuchsianSourceAction g • fuchsianTwoFixedPoint = fuchsianTwoFixedPoint ↔
      ∃ a : CyclicFour, g = Monoid.Coprod.inr a

end SphereSixComplex.TriangleGroup
