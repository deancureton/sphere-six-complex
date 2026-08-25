module

public import SphereSixComplex.Topology.FirstQuadrantTotalComplex

/-!
# The total complex of the horizontal zero column

This file supplies the missing unitor identifying the direct-sum total of a bicomplex supported
only in horizontal degree zero with its unique nonzero column.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

/-- Put a chain complex in horizontal degree zero of a first-quadrant bicomplex. -/
public noncomputable abbrev firstQuadrantSingleZeroBicomplex
    (K : FirstQuadrantChainComplex) : FirstQuadrantBicomplex :=
  (ChainComplex.single₀ (ChainComplex AddCommGrpCat ℕ)).obj K

/-- The degree-zero horizontal column is canonically the original chain complex. -/
public noncomputable def firstQuadrantSingleZeroColumnIso
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplex K).X 0 ≅ K :=
  HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) 0 K

/-- The canonical inclusion of the actual horizontal zero column into the total complex. -/
public noncomputable def firstQuadrantZeroColumnToTotal
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplex K).X 0 ⟶
      (firstQuadrantSingleZeroBicomplex K).total (ComplexShape.down ℕ) where
  f n := (firstQuadrantSingleZeroBicomplex K).ιTotal
    (ComplexShape.down ℕ) 0 n n (by simp)
  comm' := by
    intro i j hij
    change _ ≫
      ((firstQuadrantSingleZeroBicomplex K).D₁
        (ComplexShape.down ℕ) i j +
       (firstQuadrantSingleZeroBicomplex K).D₂
        (ComplexShape.down ℕ) i j) =
      ((firstQuadrantSingleZeroBicomplex K).X 0).d i j ≫ _
    rw [Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁,
      HomologicalComplex₂.ι_D₂]
    have hd₁ : (firstQuadrantSingleZeroBicomplex K).d₁
        (ComplexShape.down ℕ) 0 i j = 0 := by
      apply HomologicalComplex₂.d₁_eq_zero
      simp
    rw [hd₁, zero_add]
    rw [HomologicalComplex₂.d₂_eq
      (firstQuadrantSingleZeroBicomplex K)
      (ComplexShape.down ℕ) 0 hij j (by simp)]
    change (ComplexShape.down ℕ).ε 0 • _ = _
    rw [ComplexShape.ε_zero, one_smul]

/-- The canonical inclusion of the unique nonzero column into the total complex. -/
public noncomputable def firstQuadrantSingleZeroToTotal
    (K : FirstQuadrantChainComplex) :
    K ⟶ (firstQuadrantSingleZeroBicomplex K).total (ComplexShape.down ℕ) :=
  (firstQuadrantSingleZeroColumnIso K).inv ≫ firstQuadrantZeroColumnToTotal K

set_option backward.isDefEq.respectTransparency false in
/-- The componentwise projection used to descend from the total complex. -/
public noncomputable def firstQuadrantSingleZeroTotalComponent
    (K : FirstQuadrantChainComplex) (n p q : ℕ)
    (hpq : (ComplexShape.down ℕ).π (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q) = n) :
    ((firstQuadrantSingleZeroBicomplex K).X p).X q ⟶ K.X n := by
  rcases p with _ | p
  · change 0 + q = n at hpq
    simp only [zero_add] at hpq
    subst n
    exact (firstQuadrantSingleZeroColumnIso K).hom.f q
  · exact 0

@[simp]
public theorem firstQuadrantSingleZeroTotalComponent_zero
    (K : FirstQuadrantChainComplex) (q : ℕ) :
    firstQuadrantSingleZeroTotalComponent K q 0 q (by simp) =
      (firstQuadrantSingleZeroColumnIso K).hom.f q := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Project the total complex supported in horizontal degree zero back to its unique column. -/
public noncomputable def firstQuadrantTotalToSingleZero
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplex K).total (ComplexShape.down ℕ) ⟶ K where
  f n := (firstQuadrantSingleZeroBicomplex K).totalDesc
    (firstQuadrantSingleZeroTotalComponent K n)
  comm' := by
    intro i j hij
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    rcases p with _ | p
    · have hqi : q = i := by simpa using hpq
      subst q
      rw [← Category.assoc,
        HomologicalComplex₂.ι_totalDesc]
      simp only [firstQuadrantSingleZeroTotalComponent_zero]
      rw [(firstQuadrantSingleZeroColumnIso K).hom.comm i j]
      change ((firstQuadrantSingleZeroBicomplex K).X 0).d i j ≫
          (firstQuadrantSingleZeroColumnIso K).hom.f j =
        (firstQuadrantSingleZeroBicomplex K).ιTotal
            (ComplexShape.down ℕ) 0 i i (by simp) ≫
            ((firstQuadrantSingleZeroBicomplex K).D₁
                (ComplexShape.down ℕ) i j +
              (firstQuadrantSingleZeroBicomplex K).D₂
                (ComplexShape.down ℕ) i j) ≫ _
      rw [← Category.assoc, Preadditive.comp_add,
        HomologicalComplex₂.ι_D₁,
        HomologicalComplex₂.ι_D₂]
      have hd₁ : (firstQuadrantSingleZeroBicomplex K).d₁
          (ComplexShape.down ℕ) 0 i j = 0 := by
        apply HomologicalComplex₂.d₁_eq_zero
        simp
      rw [hd₁, zero_add]
      rw [HomologicalComplex₂.d₂_eq
        (firstQuadrantSingleZeroBicomplex K)
        (ComplexShape.down ℕ) 0 hij j (by simp)]
      simp
    · have hzcol : IsZero
          ((firstQuadrantSingleZeroBicomplex K).X (p + 1)) :=
        HomologicalComplex.isZero_single_obj_X
          (ComplexShape.down ℕ) 0 K (p + 1) (by omega)
      have hz : IsZero
          (((firstQuadrantSingleZeroBicomplex K).X (p + 1)).X q) :=
        (HomologicalComplex.eval AddCommGrpCat
          (ComplexShape.down ℕ) q).map_isZero hzcol
      exact hz.eq_of_src _ _

set_option backward.isDefEq.respectTransparency false in
/-- Projection after inclusion is the identity of the unique column. -/
public theorem firstQuadrantSingleZeroToTotal_comp_projection
    (K : FirstQuadrantChainComplex) :
    firstQuadrantSingleZeroToTotal K ≫ firstQuadrantTotalToSingleZero K =
      𝟙 K := by
  apply HomologicalComplex.Hom.ext
  funext n
  change (firstQuadrantSingleZeroBicomplex K).ιTotal
      (ComplexShape.down ℕ) 0 n n (by simp) ≫
      (firstQuadrantSingleZeroBicomplex K).totalDesc _ = 𝟙 _
  rw [HomologicalComplex₂.ι_totalDesc]
  simp [firstQuadrantSingleZeroTotalComponent,
    firstQuadrantSingleZeroColumnIso]

set_option backward.isDefEq.respectTransparency false in
/-- Inclusion after projection is the identity of the total complex. -/
public theorem firstQuadrantTotalToSingleZero_comp_inclusion
    (K : FirstQuadrantChainComplex) :
    firstQuadrantTotalToSingleZero K ≫ firstQuadrantSingleZeroToTotal K =
      𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rcases p with _ | p
  · have hqn : n = q := by simpa using hpq.symm
    cases hqn
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f]
    dsimp only [firstQuadrantTotalToSingleZero,
      firstQuadrantSingleZeroToTotal]
    rw [← Category.assoc, HomologicalComplex₂.ι_totalDesc]
    simp [firstQuadrantSingleZeroTotalComponent,
      firstQuadrantSingleZeroColumnIso]
    rfl
  · have hzcol : IsZero
        ((firstQuadrantSingleZeroBicomplex K).X (p + 1)) :=
      HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) 0 K (p + 1) (by omega)
    have hz : IsZero
        (((firstQuadrantSingleZeroBicomplex K).X (p + 1)).X q) :=
      (HomologicalComplex.eval AddCommGrpCat
        (ComplexShape.down ℕ) q).map_isZero hzcol
    exact hz.eq_of_src _ _

/-- The total of a first-quadrant bicomplex concentrated in horizontal degree zero is canonically
isomorphic to its sole column. -/
public noncomputable def firstQuadrantSingleZeroTotalIso
    (K : FirstQuadrantChainComplex) :
    (firstQuadrantSingleZeroBicomplex K).total (ComplexShape.down ℕ) ≅ K where
  hom := firstQuadrantTotalToSingleZero K
  inv := firstQuadrantSingleZeroToTotal K
  hom_inv_id := firstQuadrantTotalToSingleZero_comp_inclusion K
  inv_hom_id := firstQuadrantSingleZeroToTotal_comp_projection K

end SphereSixComplex
