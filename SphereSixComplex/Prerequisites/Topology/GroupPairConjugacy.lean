module

public import Mathlib.Algebra.Group.Opposite
public import Mathlib.Algebra.Group.Equiv.Basic

@[expose] public section
noncomputable section

namespace SphereSixComplex.Topology

/-- Two ordered pairs in a group differ by one common inner automorphism. -/
public def SimultaneouslyConjugate {G : Type*} [Group G]
    (left right : G × G) : Prop :=
  ∃ c : G, left.1 = c * right.1 * c⁻¹ ∧ left.2 = c * right.2 * c⁻¹


/-- Simultaneous conjugacy is preserved by a group homomorphism. -/
public theorem SimultaneouslyConjugate.map
    {G H : Type*} [Group G] [Group H] {left right : G × G}
    (h : SimultaneouslyConjugate left right) (f : G →* H) :
    SimultaneouslyConjugate (f left.1, f left.2) (f right.1, f right.2) := by
  obtain ⟨c, hfirst, hsecond⟩ := h
  refine ⟨f c, ?_, ?_⟩
  · simpa only [map_mul, map_inv] using congrArg f hfirst
  · simpa only [map_mul, map_inv] using congrArg f hsecond




end SphereSixComplex.Topology

end
end
