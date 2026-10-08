module

public import SphereSixComplex.Prerequisites.TriangleGroup.BinaryIndexedCoprod
public import ForMathlib.GroupTheory.CoprodI.Centralizer
import all SphereSixComplex.Prerequisites.TriangleGroup.BinaryIndexedCoprod

/-!
# Centralizers of the distinguished free-product generators

This file proves, from the indexed reduced-word normal form, that an element of
`CyclicThree * CyclicFour` commuting with either distinguished generator belongs to the
corresponding free factor.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup

open BinaryIndexedCoprod
open Monoid.CoprodI.Centralizer

/-- An element commuting with the order-three generator lies in the embedded `C₃` factor. -/
public theorem eq_inl_of_commute_g₁ (g : Delta) (h : Commute g g₁) :
    ∃ a : CyclicThree, g = Monoid.Coprod.inl a := by
  let s : DeltaFactor false := Multiplicative.ofAdd (1 : ZMod 3)
  have hs : s ≠ 1 := by
    intro h
    have h' := congrArg Multiplicative.toAdd h
    change (1 : ZMod 3) = 0 at h'
    norm_num at h'
  have hmapped : Commute (deltaToIndexed g) (Monoid.CoprodI.of s) := by
    have hmapped' := h.map deltaToIndexed
    rw [SphereSixComplex.TriangleGroup.g₁.eq_def, deltaToIndexed_inl] at hmapped'
    exact hmapped'
  obtain ⟨a, ha⟩ := eq_of_of_commute_of s hs (fun a ↦ by
      change Commute (show CyclicThree from a)
        (Multiplicative.ofAdd (1 : ZMod 3))
      exact Commute.all _ _)
    (deltaToIndexed g) hmapped
  refine ⟨a, ?_⟩
  apply deltaIndexedEquiv.injective
  change deltaToIndexed g = deltaToIndexed (Monoid.Coprod.inl a)
  exact ha.trans (deltaToIndexed_inl a).symm

/-- An element commuting with the order-four generator lies in the embedded `C₄` factor. -/
public theorem eq_inr_of_commute_g₂ (g : Delta) (h : Commute g g₂) :
    ∃ a : CyclicFour, g = Monoid.Coprod.inr a := by
  let s : DeltaFactor true := Multiplicative.ofAdd (1 : ZMod 4)
  have hs : s ≠ 1 := by
    intro h
    have h' := congrArg Multiplicative.toAdd h
    change (1 : ZMod 4) = 0 at h'
    exact (by decide : (1 : ZMod 4) ≠ 0) h'
  have hmapped : Commute (deltaToIndexed g) (Monoid.CoprodI.of s) := by
    have hmapped' := h.map deltaToIndexed
    rw [SphereSixComplex.TriangleGroup.g₂.eq_def, deltaToIndexed_inr] at hmapped'
    exact hmapped'
  obtain ⟨a, ha⟩ := eq_of_of_commute_of s hs (fun a ↦ by
      change Commute (show CyclicFour from a)
        (Multiplicative.ofAdd (1 : ZMod 4))
      exact Commute.all _ _)
    (deltaToIndexed g) hmapped
  refine ⟨a, ?_⟩
  apply deltaIndexedEquiv.injective
  change deltaToIndexed g = deltaToIndexed (Monoid.Coprod.inr a)
  exact ha.trans (deltaToIndexed_inr a).symm

end SphereSixComplex.TriangleGroup
