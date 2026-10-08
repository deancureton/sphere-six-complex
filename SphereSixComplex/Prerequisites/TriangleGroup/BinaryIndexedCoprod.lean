module

public import SphereSixComplex.Prerequisites.TriangleGroup.FreeProductTorsion
import all SphereSixComplex.Prerequisites.TriangleGroup.SourceGroup

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

/-- The canonical reduced-word type for the binary triangle group. -/
public abbrev DeltaNormalWord := Monoid.CoprodI.Word DeltaFactor

/-- Every binary triangle-group element has a unique indexed reduced-word normal form. -/
@[expose] public def deltaNormalForm : Delta ≃ DeltaNormalWord :=
  deltaIndexedEquiv.toEquiv.trans (Monoid.CoprodI.Word.equiv (M := DeltaFactor))

public theorem deltaNormalForm_prod (g : Delta) :
    (deltaNormalForm g).prod = deltaToIndexed g := by
  exact (Monoid.CoprodI.Word.equiv (M := DeltaFactor)).symm_apply_apply (deltaToIndexed g)

open Monoid.CoprodI

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
