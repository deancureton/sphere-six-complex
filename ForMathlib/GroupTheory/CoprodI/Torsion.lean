module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group

noncomputable section

namespace Monoid.CoprodI.ReducedWord

open Monoid.CoprodI

variable {I : Type*} [DecidableEq I]
variable {G : I → Type*} [∀ i, Group (G i)]

/-- Positive concatenation powers of a reduced word whose endpoint factors differ. -/
@[expose] public def cyclicPower {i j : I} (w : NeWord G i j) (hij : j ≠ i) :
    ℕ → NeWord G i j
  | 0 => w
  | n + 1 => NeWord.append (cyclicPower w hij n) hij w

omit [DecidableEq I] in
@[simp]
public theorem cyclicPower_prod {i j : I} (w : NeWord G i j) (hij : j ≠ i) (n : ℕ) :
    (cyclicPower w hij n).prod = w.prod ^ (n + 1) := by
  induction n with
  | zero => simp [cyclicPower]
  | succ n ih =>
      rw [cyclicPower, NeWord.append_prod, ih]
      simp [pow_succ]

variable [∀ i, DecidableEq (G i)]

public theorem neWord_prod_ne_one {i j : I} (w : NeWord G i j) : w.prod ≠ 1 := by
  intro hw
  have heq : w.toWord = Word.empty := by
    exact (Word.equiv (M := G)).symm.injective (by
      change w.toWord.prod = Word.empty.prod
      simpa [NeWord.prod] using hw)
  have hlist := congrArg Word.toList heq
  exact w.toList_ne_nil (by simpa [NeWord.toWord, Word.empty] using hlist)

/-- A cyclically reduced nonempty word crossing between factors has no positive trivial power. -/
public theorem cyclicallyReduced_pow_ne_one {i j : I} (w : NeWord G i j) (hij : j ≠ i)
    {n : ℕ} (hn : 0 < n) : w.prod ^ n ≠ 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [← cyclicPower_prod]
  exact neWord_prod_ne_one (cyclicPower w hij k)

/-- A cyclically reduced word involving at least two free-product factors has infinite order. -/
public theorem cyclicallyReduced_not_isOfFinOrder {i j : I} (w : NeWord G i j)
    (hij : j ≠ i) : ¬IsOfFinOrder w.prod := by
  rw [isOfFinOrder_iff_pow_eq_one]
  push Not
  exact fun n hn ↦ cyclicallyReduced_pow_ne_one w hij hn

end Monoid.CoprodI.ReducedWord

namespace Monoid.CoprodI

namespace NeWord

open Monoid.CoprodI

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)]

public theorem head_ne_one {i j : I} (w : NeWord G i j) : w.head ≠ 1 := by
  induction w with
  | singleton a ha => exact ha
  | append w₁ h w₂ ih₁ ih₂ => exact ih₁

public theorem last_ne_one {i j : I} (w : NeWord G i j) : w.last ≠ 1 := by
  induction w with
  | singleton a ha => exact ha
  | append w₁ h w₂ ih₁ ih₂ => exact ih₂

/-- A nonempty reduced word is either a singleton or a head followed by a shorter nonempty word. -/
public theorem singleton_or_head_tail {i j : I} (w : NeWord G i j) :
    (i = j ∧ w.prod = Monoid.CoprodI.of w.head ∧ w.toList.length = 1) ∨
      ∃ (k : I) (t : NeWord G k j) (_hik : i ≠ k),
        w.prod = Monoid.CoprodI.of w.head * t.prod ∧
          w.toList.length = t.toList.length + 1 := by
  induction w with
  | singleton a ha => exact Or.inl ⟨rfl, by simp, by simp⟩
  | @append i j k l w₁ hjk w₂ ih₁ ih₂ =>
      rcases ih₁ with ⟨rfl, hprod, hlen⟩ | ⟨m, t, him, hprod, hlen⟩
      · refine Or.inr ⟨k, w₂, hjk, ?_, ?_⟩
        · simpa only [Monoid.CoprodI.NeWord.append_prod,
            Monoid.CoprodI.NeWord.append_head] using congrArg (fun x ↦ x * w₂.prod) hprod
        · simp only [Monoid.CoprodI.NeWord.toList, List.length_append, hlen]
          omega
      · refine Or.inr ⟨m, .append t hjk w₂, him, ?_, ?_⟩
        · simp only [Monoid.CoprodI.NeWord.append_prod,
            Monoid.CoprodI.NeWord.append_head, hprod, mul_assoc]
        · simp only [Monoid.CoprodI.NeWord.toList, List.length_append, hlen]
          omega

/-- A nonempty reduced word is either a singleton or a shorter word followed by its last letter. -/
public theorem singleton_or_init_last {i j : I} (w : NeWord G i j) :
    (i = j ∧ w.prod = Monoid.CoprodI.of w.last ∧ w.toList.length = 1) ∨
      ∃ (k : I) (p : NeWord G i k) (_hkj : k ≠ j),
        w.prod = p.prod * Monoid.CoprodI.of w.last ∧
          w.toList.length = p.toList.length + 1 := by
  induction w with
  | singleton b hb => exact Or.inl ⟨rfl, by simp, by simp⟩
  | @append i j k l w₁ hjk w₂ ih₁ ih₂ =>
      rcases ih₂ with ⟨rfl, hprod, hlen⟩ | ⟨m, p, hml, hprod, hlen⟩
      · refine Or.inr ⟨j, w₁, hjk, ?_, ?_⟩
        · simpa only [Monoid.CoprodI.NeWord.append_prod,
            Monoid.CoprodI.NeWord.append_last] using congrArg (fun x ↦ w₁.prod * x) hprod
        · simp only [Monoid.CoprodI.NeWord.toList, List.length_append, hlen]
      · refine Or.inr ⟨m, .append w₁ hjk p, hml, ?_, ?_⟩
        · simp only [Monoid.CoprodI.NeWord.append_prod,
            Monoid.CoprodI.NeWord.append_last, hprod, mul_assoc]
        · simp only [Monoid.CoprodI.NeWord.toList, List.length_append, hlen]
          omega

end NeWord

namespace CyclicReduction

open Monoid.CoprodI

variable {I : Type*} {G : I → Type*} [∀ i, Group (G i)]

/-- The two possible nontrivial cyclic cores of a free-product element. -/
public def IsFactorConjugateOrCyclic (x : Monoid.CoprodI G) : Prop :=
  (∃ (i : I) (a : G i), a ≠ 1 ∧ IsConj x (Monoid.CoprodI.of a)) ∨
    ∃ (i j : I) (w : NeWord G i j), i ≠ j ∧ IsConj x w.prod

public theorem neWord_factor_or_cyclic_of_length (n : ℕ) :
    ∀ (i j : I) (w : NeWord G i j), w.toList.length = n →
      IsFactorConjugateOrCyclic w.prod := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro i j w hwlen
      by_cases hij : i = j
      · subst j
        rcases NeWord.singleton_or_head_tail w with hsingle | ⟨k, t, hik, hhead, hlen⟩
        · exact Or.inl ⟨i, w.head, NeWord.head_ne_one w, hsingle.2.1 ▸ IsConj.refl _⟩
        · rcases NeWord.singleton_or_init_last t with hsingle | ⟨l, p, hli, hlast, htlen⟩
          · exact (hik hsingle.1.symm).elim
          · have hconj : IsConj w.prod
                (p.prod * Monoid.CoprodI.of (t.last * w.head)) := by
              rw [isConj_iff]
              refine ⟨Monoid.CoprodI.of w.head⁻¹, ?_⟩
              rw [hhead, hlast]
              rw [map_inv, map_mul]
              group
            by_cases hba : t.last * w.head = 1
            · have hp_lt : p.toList.length < n := by omega
              have hp := ih p.toList.length hp_lt k l p rfl
              rw [hba, map_one, mul_one] at hconj
              rcases hp with ⟨m, a, ha, hp⟩ | ⟨m, q, v, hmq, hp⟩
              · exact Or.inl ⟨m, a, ha, hconj.trans hp⟩
              · exact Or.inr ⟨m, q, v, hmq, hconj.trans hp⟩
            · let v : NeWord G k i := .append p hli (.singleton (t.last * w.head) hba)
              refine Or.inr ⟨k, i, v, hik.symm, ?_⟩
              apply hconj.trans
              apply IsConj.symm
              rw [show v.prod = p.prod * Monoid.CoprodI.of (t.last * w.head) by
                simp [v]]
      · exact Or.inr ⟨i, j, w, hij, IsConj.refl _⟩

public theorem neWord_factor_or_cyclic {i j : I} (w : NeWord G i j) :
    IsFactorConjugateOrCyclic w.prod :=
  neWord_factor_or_cyclic_of_length w.toList.length i j w rfl

variable [DecidableEq I] [∀ i, DecidableEq (G i)]

/-- Every finite-order nonempty reduced word is conjugate to a nonidentity factor letter. -/
public theorem finiteOrder_neWord_isConj_factor {i j : I} (w : NeWord G i j)
    (hfin : IsOfFinOrder w.prod) :
    ∃ (k : I) (a : G k), a ≠ 1 ∧ IsConj w.prod (Monoid.CoprodI.of a) := by
  rcases neWord_factor_or_cyclic w with hfactor | ⟨k, l, v, hkl, hconj⟩
  · exact hfactor
  · exact (ReducedWord.cyclicallyReduced_not_isOfFinOrder v hkl.symm
      (hconj.isOfFinOrder hfin)).elim

/-- Every nonidentity finite-order element of an indexed free product is conjugate into a factor. -/
public theorem finiteOrder_isConj_factor (x : Monoid.CoprodI G) (hfin : IsOfFinOrder x)
    (hx : x ≠ 1) :
    ∃ (i : I) (a : G i), a ≠ 1 ∧ IsConj x (Monoid.CoprodI.of a) := by
  let word := Monoid.CoprodI.Word.equiv (M := G) x
  have hword : word ≠ Monoid.CoprodI.Word.empty := by
    intro heq
    have hone : (Monoid.CoprodI.Word.equiv (M := G)) (1 : Monoid.CoprodI G) =
        Monoid.CoprodI.Word.empty := by simp [Monoid.CoprodI.Word.equiv]
    exact hx ((Monoid.CoprodI.Word.equiv (M := G)).injective (heq.trans hone.symm))
  obtain ⟨i, j, w, hw⟩ := Monoid.CoprodI.NeWord.of_word word hword
  have hprod : w.prod = x := by
    change w.toWord.prod = x
    rw [hw]
    exact (Monoid.CoprodI.Word.equiv (M := G)).symm_apply_apply x
  obtain ⟨k, a, ha, hconj⟩ := finiteOrder_neWord_isConj_factor w (hprod ▸ hfin)
  exact ⟨k, a, ha, hprod ▸ hconj⟩

end CyclicReduction

end Monoid.CoprodI
