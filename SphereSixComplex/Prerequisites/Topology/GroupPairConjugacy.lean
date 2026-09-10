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

public theorem simultaneouslyConjugate_refl {G : Type*} [Group G] (p : G × G) :
    SimultaneouslyConjugate p p := by
  refine ⟨1, ?_, ?_⟩ <;> simp

/-- Simultaneous conjugacy is preserved by a group homomorphism. -/
public theorem SimultaneouslyConjugate.map
    {G H : Type*} [Group G] [Group H] {left right : G × G}
    (h : SimultaneouslyConjugate left right) (f : G →* H) :
    SimultaneouslyConjugate (f left.1, f left.2) (f right.1, f right.2) := by
  obtain ⟨c, hfirst, hsecond⟩ := h
  refine ⟨f c, ?_, ?_⟩
  · simpa only [map_mul, map_inv] using congrArg f hfirst
  · simpa only [map_mul, map_inv] using congrArg f hsecond

/-- Passing from an opposite group back to the original group preserves simultaneous
conjugacy, with the inverse conjugator. -/
public theorem SimultaneouslyConjugate.unop
    {G : Type*} [Group G] {left right : Gᵐᵒᵖ × Gᵐᵒᵖ}
    (h : SimultaneouslyConjugate left right) :
    SimultaneouslyConjugate
      (MulOpposite.unop left.1, MulOpposite.unop left.2)
      (MulOpposite.unop right.1, MulOpposite.unop right.2) := by
  obtain ⟨c, hfirst, hsecond⟩ := h
  refine ⟨(MulOpposite.unop c)⁻¹, ?_, ?_⟩
  · rw [mul_assoc]
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_inv, inv_inv] using
      congrArg MulOpposite.unop hfirst
  · rw [mul_assoc]
    simpa only [MulOpposite.unop_mul, MulOpposite.unop_inv, inv_inv] using
      congrArg MulOpposite.unop hsecond

/-- Passing to the opposite group also preserves simultaneous conjugacy. -/
public theorem SimultaneouslyConjugate.op
    {G : Type*} [Group G] {left right : G × G}
    (h : SimultaneouslyConjugate left right) :
    SimultaneouslyConjugate
      (MulOpposite.op left.1, MulOpposite.op left.2)
      (MulOpposite.op right.1, MulOpposite.op right.2) := by
  obtain ⟨c, hfirst, hsecond⟩ := h
  refine ⟨(MulOpposite.op c)⁻¹, ?_, ?_⟩
  · rw [mul_assoc]
    simpa only [MulOpposite.op_mul, MulOpposite.op_inv, inv_inv] using
      congrArg MulOpposite.op hfirst
  · rw [mul_assoc]
    simpa only [MulOpposite.op_mul, MulOpposite.op_inv, inv_inv] using
      congrArg MulOpposite.op hsecond

/-- A group equivalence reflects simultaneous conjugacy as well as preserving it. -/
public theorem simultaneouslyConjugate_map_equiv_iff
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (left right : G × G) :
    SimultaneouslyConjugate (e left.1, e left.2) (e right.1, e right.2) ↔
      SimultaneouslyConjugate left right := by
  constructor
  · intro h
    obtain ⟨c, hfirst, hsecond⟩ := h
    refine ⟨e.symm c, ?_, ?_⟩
    · apply e.injective
      simpa only [map_mul, map_inv, e.apply_symm_apply] using hfirst
    · apply e.injective
      simpa only [map_mul, map_inv, e.apply_symm_apply] using hsecond
  · intro h
    exact h.map e.toMonoidHom

end SphereSixComplex.Topology

end
end
