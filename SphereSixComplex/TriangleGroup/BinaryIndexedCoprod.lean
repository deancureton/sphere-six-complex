module

public import SphereSixComplex.TriangleGroup.FreeProductTorsion
public import Mathlib.GroupTheory.CoprodI
import all SphereSixComplex.TriangleGroup.Representation

/-!
# Indexed reduced words for the binary triangle-group coproduct

Mathlib's binary coproduct and indexed coproduct have separate implementations.  This file builds
the concrete equivalence needed for `Delta = C₃ * C₄`, proves its computation rules on both
injections, and transfers the indexed reduced-word normal form to `Delta`.
-/

noncomputable section

namespace SphereSixComplex.TriangleGroup.BinaryIndexedCoprod

open SphereSixComplex.TriangleGroup

/-- The two cyclic factors of `Delta`, in the order used by its binary coproduct. -/
@[expose] public def DeltaFactor : Bool → Type
  | false => CyclicThree
  | true => CyclicFour

public instance (b : Bool) : Group (DeltaFactor b) := by
  cases b <;> simp only [DeltaFactor] <;> infer_instance

public instance (b : Bool) : DecidableEq (DeltaFactor b) := by
  cases b <;> simp only [DeltaFactor] <;> infer_instance

/-- The binary presentation maps to the indexed presentation by the two canonical injections. -/
@[expose] public def deltaToIndexed : Delta →* Monoid.CoprodI DeltaFactor :=
  Monoid.Coprod.lift
    (Monoid.CoprodI.of : DeltaFactor false →* Monoid.CoprodI DeltaFactor)
    (Monoid.CoprodI.of : DeltaFactor true →* Monoid.CoprodI DeltaFactor)

/-- The indexed presentation maps back to the binary presentation by the two injections. -/
@[expose] public def indexedToDelta : Monoid.CoprodI DeltaFactor →* Delta :=
  Monoid.CoprodI.lift fun
    | false => (Monoid.Coprod.inl : CyclicThree →* Delta)
    | true => (Monoid.Coprod.inr : CyclicFour →* Delta)

@[simp]
public theorem deltaToIndexed_inl (a : CyclicThree) :
    deltaToIndexed (Monoid.Coprod.inl a) =
      (Monoid.CoprodI.of : DeltaFactor false →* Monoid.CoprodI DeltaFactor) a :=
  rfl

@[simp]
public theorem deltaToIndexed_inr (a : CyclicFour) :
    deltaToIndexed (Monoid.Coprod.inr a) =
      (Monoid.CoprodI.of : DeltaFactor true →* Monoid.CoprodI DeltaFactor) a :=
  rfl

@[simp]
public theorem indexedToDelta_of_false (a : DeltaFactor false) :
    indexedToDelta
        ((Monoid.CoprodI.of : DeltaFactor false →* Monoid.CoprodI DeltaFactor) a) =
      Monoid.Coprod.inl a :=
  rfl

@[simp]
public theorem indexedToDelta_of_true (a : DeltaFactor true) :
    indexedToDelta
        ((Monoid.CoprodI.of : DeltaFactor true →* Monoid.CoprodI DeltaFactor) a) =
      Monoid.Coprod.inr a :=
  rfl

public theorem indexedToDelta_comp_deltaToIndexed :
    indexedToDelta.comp deltaToIndexed = MonoidHom.id Delta := by
  apply Monoid.Coprod.hom_ext
  · apply MonoidHom.ext
    intro a
    exact indexedToDelta_of_false a
  · apply MonoidHom.ext
    intro a
    exact indexedToDelta_of_true a

public theorem deltaToIndexed_comp_indexedToDelta :
    deltaToIndexed.comp indexedToDelta = MonoidHom.id (Monoid.CoprodI DeltaFactor) := by
  apply Monoid.CoprodI.ext_hom
  intro b
  apply MonoidHom.ext
  intro a
  cases b
  · exact deltaToIndexed_inl a
  · exact deltaToIndexed_inr a

/-- Multiplicative equivalence between the binary and indexed presentations of `Delta`. -/
@[expose] public def deltaIndexedEquiv : Delta ≃* Monoid.CoprodI DeltaFactor where
  toFun := deltaToIndexed
  invFun := indexedToDelta
  left_inv g := DFunLike.congr_fun indexedToDelta_comp_deltaToIndexed g
  right_inv g := DFunLike.congr_fun deltaToIndexed_comp_indexedToDelta g
  map_mul' := map_mul deltaToIndexed

@[simp]
public theorem deltaIndexedEquiv_apply (g : Delta) : deltaIndexedEquiv g = deltaToIndexed g :=
  rfl

@[simp]
public theorem deltaIndexedEquiv_symm_apply (g : Monoid.CoprodI DeltaFactor) :
    deltaIndexedEquiv.symm g = indexedToDelta g :=
  rfl

/-- The canonical reduced-word type for the binary triangle group. -/
public abbrev DeltaNormalWord := Monoid.CoprodI.Word DeltaFactor

/-- Every binary triangle-group element has a unique indexed reduced-word normal form. -/
@[expose] public def deltaNormalForm : Delta ≃ DeltaNormalWord :=
  deltaIndexedEquiv.toEquiv.trans (Monoid.CoprodI.Word.equiv (M := DeltaFactor))

public theorem deltaNormalForm_prod (g : Delta) :
    (deltaNormalForm g).prod = deltaToIndexed g := by
  exact (Monoid.CoprodI.Word.equiv (M := DeltaFactor)).symm_apply_apply (deltaToIndexed g)

public theorem indexed_cyclicallyReduced_not_isOfFinOrder {i j : Bool}
    (w : Monoid.CoprodI.NeWord DeltaFactor i j) (hij : j ≠ i) :
    ¬IsOfFinOrder (indexedToDelta w.prod) := by
  rw [← deltaIndexedEquiv.injective.isOfFinOrder_iff]
  change ¬IsOfFinOrder ((deltaToIndexed.comp indexedToDelta) w.prod)
  rw [DFunLike.congr_fun deltaToIndexed_comp_indexedToDelta w.prod]
  exact FreeProductTorsion.ReducedWord.cyclicallyReduced_not_isOfFinOrder w hij

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
  · exact (FreeProductTorsion.ReducedWord.cyclicallyReduced_not_isOfFinOrder v hkl.symm
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

/-- Every nonidentity finite-order triangle-group element is conjugate into `C₃` or `C₄`. -/
public theorem finiteOrder_isConj_inl_or_inr (g : Delta) (hfin : IsOfFinOrder g) (hg : g ≠ 1) :
    (∃ a : CyclicThree, a ≠ 1 ∧ IsConj g (Monoid.Coprod.inl a)) ∨
      ∃ a : CyclicFour, a ≠ 1 ∧ IsConj g (Monoid.Coprod.inr a) := by
  have hindexed_ne : deltaToIndexed g ≠ 1 := by
    intro h
    apply hg
    apply deltaIndexedEquiv.injective
    simpa using h
  obtain ⟨i, a, ha, hconj⟩ := CyclicReduction.finiteOrder_isConj_factor
    (deltaToIndexed g) (deltaToIndexed.isOfFinOrder hfin) hindexed_ne
  have hleft : indexedToDelta (deltaToIndexed g) = g :=
    DFunLike.congr_fun indexedToDelta_comp_deltaToIndexed g
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hmapped : IsConj g (indexedToDelta (Monoid.CoprodI.of a)) := by
    rw [isConj_iff]
    refine ⟨indexedToDelta c, ?_⟩
    calc
      indexedToDelta c * g * (indexedToDelta c)⁻¹ =
          indexedToDelta c * indexedToDelta (deltaToIndexed g) *
            indexedToDelta c⁻¹ := by rw [hleft, map_inv]
      _ = indexedToDelta (c * deltaToIndexed g * c⁻¹) := by simp
      _ = indexedToDelta (Monoid.CoprodI.of a) := congrArg indexedToDelta hc
  cases i with
  | false =>
      have hof := indexedToDelta_of_false a
      rw [hof] at hmapped
      exact Or.inl ⟨a, ha, hmapped⟩
  | true =>
      have hof := indexedToDelta_of_true a
      rw [hof] at hmapped
      exact Or.inr ⟨a, ha, hmapped⟩

/-- Explicit conjugacy form of the finite-order classification. -/
public theorem finiteOrder_eq_conjugate_factor (g : Delta) (hfin : IsOfFinOrder g) (hg : g ≠ 1) :
    (∃ (c : Delta) (a : CyclicThree), a ≠ 1 ∧
        g = c * Monoid.Coprod.inl a * c⁻¹) ∨
      ∃ (c : Delta) (a : CyclicFour), a ≠ 1 ∧
        g = c * Monoid.Coprod.inr a * c⁻¹ := by
  rcases finiteOrder_isConj_inl_or_inr g hfin hg with
    ⟨a, ha, hconj⟩ | ⟨a, ha, hconj⟩
  · obtain ⟨c, hc⟩ := isConj_iff.mp hconj.symm
    exact Or.inl ⟨c, a, ha, hc.symm⟩
  · obtain ⟨c, hc⟩ := isConj_iff.mp hconj.symm
    exact Or.inr ⟨c, a, ha, hc.symm⟩

/-- A finite-order element fixing a regular point of the explicit Fuchsian action is trivial. -/
public theorem finiteOrder_fixed_regular_eq_one {g : Delta} {z : UpperHalfPlane}
    (hz : FreeProductTorsion.IsFuchsianRegularPoint z) (hfin : IsOfFinOrder g)
    (hfixed : fuchsianSourceAction g • z = z) : g = 1 := by
  by_contra hg
  rcases finiteOrder_eq_conjugate_factor g hfin hg with
    ⟨c, a, ha, rfl⟩ | ⟨c, a, ha, rfl⟩
  · exact FreeProductTorsion.regular_not_fixed_by_conjugate_inl hz c a ha hfixed
  · exact FreeProductTorsion.regular_not_fixed_by_conjugate_inr hz c a ha hfixed

end SphereSixComplex.TriangleGroup.BinaryIndexedCoprod
