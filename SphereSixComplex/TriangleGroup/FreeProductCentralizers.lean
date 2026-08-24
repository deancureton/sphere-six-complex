module

public import SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
import all SphereSixComplex.TriangleGroup.BinaryIndexedCoprod

/-!
# Centralizers of the distinguished free-product generators

This file proves, from the indexed reduced-word normal form, that an element of
`CyclicThree * CyclicFour` commuting with either distinguished generator belongs to the
corresponding free factor.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup.FreeProductCentralizers

open SphereSixComplex.TriangleGroup
open BinaryIndexedCoprod
open Monoid.CoprodI

variable {I : Type*} {G : I → Type*} [DecidableEq I]
variable [∀ i, Group (G i)] [∀ i, DecidableEq (G i)]

/-- Two nonempty reduced words with equal products are the same reduced word. -/
private theorem neWord_toWord_eq_of_prod_eq {i j k l : I}
    {u : NeWord G i j} {v : NeWord G k l} (h : u.prod = v.prod) :
    u.toWord = v.toWord := by
  apply (Word.equiv (M := G)).symm.injective
  change u.toWord.prod = v.toWord.prod
  exact h

/-- A reduced word whose last factor differs from that of a nonidentity letter cannot commute
with that letter. -/
public theorem neWord_not_commute_of_last_ne {i j k : I} (w : NeWord G i j)
    (s : G k) (hjk : j ≠ k) (hs : s ≠ 1) :
    ¬Commute w.prod (Monoid.CoprodI.of s) := by
  let single : NeWord G k k := .singleton s hs
  let middle : NeWord G i k := .append w hjk single
  let conjugate : NeWord G i i := .append middle hjk.symm w.inv
  intro hcomm
  have hprod : conjugate.prod = single.prod := by
    simp only [conjugate, middle, NeWord.append_prod, NeWord.inv_prod]
    exact hcomm.mul_inv_cancel
  have hword : conjugate.toWord = single.toWord :=
    neWord_toWord_eq_of_prod_eq hprod
  have hlen := congrArg (fun q : Word G ↦ q.toList.length) hword
  have hwpos : 0 < w.toList.length := List.length_pos_of_ne_nil w.toList_ne_nil
  simp only [conjugate, middle, NeWord.toWord, NeWord.toList, List.length_append] at hlen
  omega

/-- In an indexed free product, if every element of one factor commutes with a fixed nonidentity
letter of that factor, then its centralizer is contained in the factor. -/
public theorem eq_of_of_commute_of {k : I} (s : G k) (hs : s ≠ 1)
    (hfactor : ∀ a : G k, Commute a s) (x : Monoid.CoprodI G)
    (hx : Commute x (Monoid.CoprodI.of s)) :
    ∃ a : G k, x = Monoid.CoprodI.of a := by
  let word := Word.equiv (M := G) x
  have hwordProd : word.prod = x := by
    exact (Word.equiv (M := G)).symm_apply_apply x
  by_cases hword : word = Word.empty
  · refine ⟨1, ?_⟩
    rw [hword, Word.prod_empty] at hwordProd
    simpa only [map_one] using hwordProd.symm
  · obtain ⟨i, j, w, hw⟩ := NeWord.of_word word hword
    have hprod : w.prod = x := by
      change w.toWord.prod = x
      rw [hw]
      exact hwordProd
    have hwcomm : Commute w.prod (Monoid.CoprodI.of s) := by
      simpa only [hprod] using hx
    by_cases hjk : j = k
    · subst j
      rcases BinaryIndexedCoprod.NeWord.singleton_or_init_last w with
        hsingle | ⟨l, p, hlk, hsplit, _⟩
      · refine ⟨w.last, ?_⟩
        exact hprod.symm.trans hsingle.2.1
      · have hletter : Commute (Monoid.CoprodI.of w.last) (Monoid.CoprodI.of s) :=
          (hfactor w.last).map (Monoid.CoprodI.of : G k →* Monoid.CoprodI G)
        have hwhole : Commute (p.prod * Monoid.CoprodI.of w.last)
            (Monoid.CoprodI.of s) := by
          simpa only [hsplit] using hwcomm
        have hpcomm : Commute p.prod (Monoid.CoprodI.of s) := by
          have hcancel := hwhole.mul_left hletter.inv_left
          simpa only [mul_assoc, mul_inv_cancel, mul_one] using hcancel
        exact (neWord_not_commute_of_last_ne p s hlk hs hpcomm).elim
    · exact (neWord_not_commute_of_last_ne w s hjk hs hwcomm).elim

end SphereSixComplex.TriangleGroup.FreeProductCentralizers

namespace SphereSixComplex.TriangleGroup

open BinaryIndexedCoprod
open FreeProductCentralizers

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

/-- Exact centralizer membership criterion for the order-three generator. -/
public theorem commute_g₁_iff_eq_inl (g : Delta) :
    Commute g g₁ ↔ ∃ a : CyclicThree, g = Monoid.Coprod.inl a := by
  constructor
  · exact eq_inl_of_commute_g₁ g
  · rintro ⟨a, rfl⟩
    rw [SphereSixComplex.TriangleGroup.g₁.eq_def]
    exact (Commute.all a (Multiplicative.ofAdd (1 : ZMod 3))).map
      (Monoid.Coprod.inl : CyclicThree →* Delta)

/-- Exact centralizer membership criterion for the order-four generator. -/
public theorem commute_g₂_iff_eq_inr (g : Delta) :
    Commute g g₂ ↔ ∃ a : CyclicFour, g = Monoid.Coprod.inr a := by
  constructor
  · exact eq_inr_of_commute_g₂ g
  · rintro ⟨a, rfl⟩
    rw [SphereSixComplex.TriangleGroup.g₂.eq_def]
    exact (Commute.all a (Multiplicative.ofAdd (1 : ZMod 4))).map
      (Monoid.Coprod.inr : CyclicFour →* Delta)

end SphereSixComplex.TriangleGroup
