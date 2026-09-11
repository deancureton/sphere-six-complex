module

public import SphereSixComplex.Prerequisites.Topology.SmoothRecognition
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# Four-piece Mayer--Vietoris interface

Mathlib currently has no singular-homology excision or Mayer--Vietoris theorem. This file records
the exact long-sequence segments needed for an ordered four-piece cover and isolates the remaining
calculation as a quasi-isomorphism of integral singular chain complexes.
-/

@[expose] public section

noncomputable section

open AlgebraicTopology CategoryTheory Set
open scoped ContinuousMap

namespace SphereSixComplex



/-- The map on integral singular homology induced by a continuous map. -/
public noncomputable def integralSingularHomologyMap
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (k : ℕ) (f : C(X, Y)) :
    IntegralSingularHomology k X →+ IntegralSingularHomology k Y :=
  ConcreteCategory.hom
    (((singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)).map
      (TopCat.ofHom f))

/-- An ordered cover by the four pieces used in the construction. -/
public structure FourPieceOpenCover (X : Type) [TopologicalSpace X] where
  /-- The four open pieces. -/
  piece : Fin 4 → Set X
  /-- Every piece is open. -/
  isOpen_piece : ∀ i, IsOpen (piece i)
  /-- The pieces cover the whole space. -/
  covers : ⋃ i, piece i = Set.univ

namespace FourPieceOpenCover

/-- The union of the pieces up to and including `r`. -/
public def stage {X : Type} [TopologicalSpace X] (C : FourPieceOpenCover X) (r : Fin 4) :
    Set X :=
  ⋃ i : Fin 4, ⋃ _ : i ≤ r, C.piece i

/-- Every partial union is open. -/
public theorem isOpen_stage {X : Type} [TopologicalSpace X] (C : FourPieceOpenCover X)
    (r : Fin 4) : IsOpen (C.stage r) := by
  exact isOpen_iUnion fun i ↦ isOpen_iUnion fun _ ↦ C.isOpen_piece i

/-- Adjoining the next piece produces the next partial union. -/
public theorem stage_union_next {X : Type} [TopologicalSpace X] (C : FourPieceOpenCover X)
    (r : Fin 3) : C.stage r.castSucc ∪ C.piece r.succ = C.stage r.succ := by
  ext x
  simp only [stage, mem_union, mem_iUnion]
  constructor
  · rintro (⟨i, hi, hx⟩ | hx)
    · exact ⟨i, hi.trans (Fin.castSucc_le_succ r), hx⟩
    · exact ⟨r.succ, le_rfl, hx⟩
  · rintro ⟨i, hi, hx⟩
    by_cases hle : i ≤ r.castSucc
    · exact Or.inl ⟨i, hle, hx⟩
    · right
      have hnotlt : ¬ i < r.succ := fun hlt ↦ hle (Fin.le_castSucc_iff.mpr hlt)
      have h : i = r.succ := le_antisymm hi (le_of_not_gt hnotlt)
      simpa only [h] using hx

/-- The last partial union is the whole space. -/
@[simp]
public theorem stage_last {X : Type} [TopologicalSpace X] (C : FourPieceOpenCover X) :
    C.stage ⟨3, by omega⟩ = Set.univ := by
  rw [← C.covers]
  ext x
  simp only [stage, mem_iUnion]
  constructor
  · rintro ⟨i, -, hx⟩
    exact ⟨i, hx⟩
  · rintro ⟨i, hx⟩
    exact ⟨i, Fin.le_last i, hx⟩


end FourPieceOpenCover

namespace IntegralMayerVietoris

variable {X : Type} [TopologicalSpace X] (A B : Set X)

/-- Inclusion of the overlap into the left member of a binary cover. -/
public def interToLeft : C((A ∩ B : Set X), A) where
  toFun x := ⟨x.1, x.2.1⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion of the overlap into the right member of a binary cover. -/
public def interToRight : C((A ∩ B : Set X), B) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion of the left member into the union. -/
public def leftToUnion : C(A, (A ∪ B : Set X)) where
  toFun x := ⟨x.1, Or.inl x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Inclusion of the right member into the union. -/
public def rightToUnion : C(B, (A ∪ B : Set X)) where
  toFun x := ⟨x.1, Or.inr x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The signed map from overlap homology to the homology of the two pieces. -/
public noncomputable def differenceMap (k : ℕ) :
    IntegralSingularHomology k (A ∩ B : Set X) →+
      IntegralSingularHomology k A × IntegralSingularHomology k B :=
  (integralSingularHomologyMap k (interToLeft A B)).prod
    (-(integralSingularHomologyMap k (interToRight A B)))

/-- The sum of the two inclusion maps from piece homology to union homology. -/
public noncomputable def sumMap (k : ℕ) :
    IntegralSingularHomology k A × IntegralSingularHomology k B →+
      IntegralSingularHomology k (A ∪ B : Set X) where
  toFun z := integralSingularHomologyMap k (leftToUnion A B) z.1 +
    integralSingularHomologyMap k (rightToUnion A B) z.2
  map_zero' := by simp
  map_add' := by
    intro x y
    change
      integralSingularHomologyMap k (leftToUnion A B) (x.1 + y.1) +
          integralSingularHomologyMap k (rightToUnion A B) (x.2 + y.2) = _
    rw [map_add, map_add]
    abel

/-- The five-term exact portion of the integral Mayer--Vietoris sequence, including connecting
maps, in every nonnegative degree. -/
public def ExactSequence : Prop :=
  ∃ boundary : ∀ k : ℕ,
      IntegralSingularHomology (k + 1) (A ∪ B : Set X) →+
        IntegralSingularHomology k (A ∩ B : Set X),
    ∀ k : ℕ,
      Function.Exact (sumMap A B (k + 1)) (boundary k) ∧
      Function.Exact (boundary k) (differenceMap A B k) ∧
      Function.Exact (differenceMap A B k) (sumMap A B k)

end IntegralMayerVietoris

/-- Exact Mayer--Vietoris data for the three successive binary unions of an ordered four-piece
cover. This is the excision-dependent theorem currently absent from mathlib. -/
public def FourPieceMayerVietorisExactness
    {X : Type} [TopologicalSpace X] (C : FourPieceOpenCover X) : Prop :=
  ∀ r : Fin 3,
    IntegralMayerVietoris.ExactSequence (C.stage r.castSucc) (C.piece r.succ)










end SphereSixComplex
