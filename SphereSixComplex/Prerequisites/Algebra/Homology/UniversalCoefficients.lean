/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Kronecker
public import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Universal coefficients for complexes with projective lower homology

The Kronecker arguments adapt `TauCeti.Algebra.Homology.Kronecker` from injective
coefficients to split cycle and boundary inclusions.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace CategoryTheory

variable {C : Type*} [Category* C] [Abelian C]

lemma isSplitMono_factorThruCoimage_of_regular {A B : C} (f : A ⟶ B) (s : B ⟶ A)
    (h : f ≫ s ≫ f = f) : IsSplitMono (Abelian.factorThruCoimage f) := by
  refine IsSplitMono.mk' ⟨s ≫ Abelian.coimage.π f, ?_⟩
  rw [← cancel_epi (Abelian.coimage.π f), ← cancel_mono (Abelian.factorThruCoimage f)]
  simpa using h

end CategoryTheory

namespace TauCeti.ChainComplex

variable {C : Type*} [Category* C] [Abelian C] {k : Type*} [Ring k] [Linear k C]
  {X : ChainComplex C ℕ} {Y : C}

lemma isSplitMono_iCycles_of_regular (i : ℕ)
    (s : X.X ((ComplexShape.down ℕ).next i) ⟶ X.X i)
    (h : X.d i ((ComplexShape.down ℕ).next i) ≫ s ≫
      X.d i ((ComplexShape.down ℕ).next i) = X.d i ((ComplexShape.down ℕ).next i)) :
    IsSplitMono (X.iCycles i) := by
  let r := X.liftCycles (𝟙 (X.X i) - X.d i ((ComplexShape.down ℕ).next i) ≫ s)
    _ rfl (by simp [h])
  refine IsSplitMono.mk' ⟨r, ?_⟩
  rw [← cancel_mono (X.iCycles i)]
  simp [r]

lemma exists_regular_d [∀ i, Projective (X.X i)] (n : ℕ)
    (hH : ∀ j < n, Projective (X.homology j)) :
    ∃ s : X.X ((ComplexShape.down ℕ).next n) ⟶ X.X n,
      X.d n ((ComplexShape.down ℕ).next n) ≫ s ≫ X.d n ((ComplexShape.down ℕ).next n) =
        X.d n ((ComplexShape.down ℕ).next n) := by
  induction n with
  | zero =>
    refine ⟨0, ?_⟩
    simp
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih (fun j hj ↦ hH j (Nat.lt_succ_of_lt hj))
    let := isSplitMono_iCycles_of_regular n s hs
    let : Projective (X.cycles n) :=
      (show Retract (X.cycles n) (X.X n) from
        ⟨X.iCycles n, retraction (X.iCycles n), by simp⟩).projective
    let := hH n (Nat.lt_succ_self n)
    let sectionH := Projective.factorThru (𝟙 (X.homology n)) (X.homologyπ n)
    let S := ShortComplex.mk (X.toCycles (n + 1) n) (X.homologyπ n) (by simp)
    have hS : S.Exact := S.exact_of_g_is_cokernel
      (X.homologyIsCokernel (n + 1) n (by simp))
    let p := 𝟙 (X.cycles n) - X.homologyπ n ≫ sectionH
    have hp : p ≫ X.homologyπ n = 0 := by simp [p, sectionH]
    let t := hS.liftFromProjective p hp
    have ht : t ≫ X.toCycles (n + 1) n = p := hS.liftFromProjective_comp p hp
    rw [(ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)]
    refine ⟨retraction (X.iCycles n) ≫ t, ?_⟩
    change X.d (n + 1) n ≫ (retraction (X.iCycles n) ≫ t) ≫
      X.d (n + 1) n = X.d (n + 1) n
    rw [← X.toCycles_i (n + 1) n]
    simp only [Category.assoc, IsSplitMono.id_assoc, ← Category.assoc t, ht]
    simp [p]

lemma kronecker_surjective_of_isSplitMono (i : ℕ) [IsSplitMono (X.iCycles i)] :
    Function.Surjective (kronecker k X Y i) := by
  intro g
  let φ : X.X i ⟶ Y := retraction (X.iCycles i) ≫ X.homologyπ i ≫ g
  have hφ : X.iCycles i ≫ φ = X.homologyπ i ≫ g := by simp [φ]
  refine ⟨(X.linearYonedaObj k Y).homologyπ i
    ((X.linearYonedaObj k Y).moduleCatCyclesMk φ _ rfl ?_), ?_⟩
  · refine (linearYonedaObj_d_apply i _ φ).trans ?_
    rw [← X.toCycles_i, Category.assoc, hφ, toCycles_comp_homologyπ_assoc, zero_comp]
    rfl
  · rw [← cancel_epi (X.homologyπ i), kronecker_homologyπ]
    exact (congrArg (X.iCycles i ≫ ·) (iCycles_moduleCatCyclesMk ..)).trans hφ

lemma kronecker_injective_of_isSplitMono (i : ℕ)
    [IsSplitMono (Abelian.factorThruCoimage (X.d i ((ComplexShape.down ℕ).next i)))] :
    Function.Injective (kronecker k X Y i) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨φ, rfl⟩ := HomologicalComplex.moduleCat_homologyπ_surjective _ i x
  obtain ⟨a, ha⟩ : ∃ a : X.X i ⟶ Y, (X.linearYonedaObj k Y).iCycles i φ = a := ⟨_, rfl⟩
  let j := (ComplexShape.down ℕ).next i
  have hcyc : X.iCycles i ≫ a = 0 := by
    rw [← ha, ← kronecker_homologyπ, hx, comp_zero]
  have hker : kernel.ι (X.d i j) ≫ a = 0 := by
    rw [← X.liftCycles_i (kernel.ι (X.d i j)) j rfl (kernel.condition _), Category.assoc,
      hcyc, comp_zero]
  let b : X.X j ⟶ Y := retraction (Abelian.factorThruCoimage (X.d i j)) ≫
    cokernel.desc _ a hker
  have hb : X.d i j ≫ b = a := by
    dsimp [b]
    conv_lhs => lhs; rw [← Abelian.coimage.fac (X.d i j)]
    rw [Category.assoc, IsSplitMono.id_assoc, cokernel.π_desc]
  have hφ : (X.linearYonedaObj k Y).toCycles j i b = φ :=
    HomologicalComplex.moduleCat_iCycles_injective _ _
      ((linearYonedaObj_iCycles_toCycles_apply j i b).trans (hb.trans ha.symm))
  rw [← hφ]
  exact linearYonedaObj_homologyπ_toCycles_apply j i b

/-- The Kronecker map is bijective when the chain objects and all lower homology
objects are projective. This includes degree zero without a homology hypothesis. -/
theorem kronecker_bijective_of_projective [∀ i, Projective (X.X i)] (n : ℕ)
    (hH : ∀ j < n, Projective (X.homology j)) :
    Function.Bijective (kronecker k X Y n) := by
  obtain ⟨s, hs⟩ := exists_regular_d n hH
  let := isSplitMono_iCycles_of_regular n s hs
  let := isSplitMono_factorThruCoimage_of_regular _ s hs
  exact ⟨kronecker_injective_of_isSplitMono n, kronecker_surjective_of_isSplitMono n⟩

variable (k X Y) in
/-- Universal coefficients for a complex of projective objects with projective homology
in lower degrees, with arbitrary coefficients. -/
def kroneckerEquivOfProjective [∀ i, Projective (X.X i)] (n : ℕ)
    (hH : ∀ j < n, Projective (X.homology j)) :
    (X.linearYonedaObj k Y).homology n ≃ₗ[k] (X.homology n ⟶ Y) :=
  LinearEquiv.ofBijective (kronecker k X Y n) (kronecker_bijective_of_projective n hH)

end TauCeti.ChainComplex
