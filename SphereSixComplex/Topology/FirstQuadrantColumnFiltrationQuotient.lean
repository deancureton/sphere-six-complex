module

public import SphereSixComplex.Topology.FirstQuadrantColumnFiltration

/-!
# Successive column quotients of finite first-quadrant prefixes

The `(n + 1)`st prefix has a canonical projection to its last column, regarded as a bicomplex
concentrated in outer degree `n + 1`.  This is the quotient map in the finite column filtration.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace SphereSixComplex

/-- A single outer column of a first-quadrant bicomplex. -/
public noncomputable abbrev firstQuadrantSingleColumn
    (K : FirstQuadrantBicomplex) (p : ℕ) : FirstQuadrantBicomplex :=
  (HomologicalComplex.single (ChainComplex AddCommGrpCat ℕ)
    (ComplexShape.down ℕ) p).obj (K.X p)

/-- The unique nonzero outer column is canonically the original column. -/
public noncomputable def firstQuadrantSingleColumnXIso
    (K : FirstQuadrantBicomplex) (p : ℕ) :
    (firstQuadrantSingleColumn K p).X p ≅ K.X p :=
  HomologicalComplex.singleObjXSelf (ComplexShape.down ℕ) p (K.X p)

/-- Component of the projection from the prefix ending at `p` to its last column. -/
public noncomputable def firstQuadrantColumnPrefixToLastComponent
    (K : FirstQuadrantBicomplex) (p q : ℕ) :
    (firstQuadrantColumnPrefix K p).X q ⟶
      (firstQuadrantSingleColumn K p).X q := by
  by_cases hq : q = p
  · subst q
    exact (firstQuadrantColumnPrefixXIso K p p le_rfl).hom ≫
      (firstQuadrantSingleColumnXIso K p).inv
  · exact 0

@[simp]
public theorem firstQuadrantColumnPrefixToLastComponent_self
    (K : FirstQuadrantBicomplex) (p : ℕ) :
    firstQuadrantColumnPrefixToLastComponent K p p =
      (firstQuadrantColumnPrefixXIso K p p le_rfl).hom ≫
        (firstQuadrantSingleColumnXIso K p).inv := by
  simp [firstQuadrantColumnPrefixToLastComponent]

public theorem firstQuadrantColumnPrefixToLastComponent_eq_zero
    (K : FirstQuadrantBicomplex) (p q : ℕ) (hq : q ≠ p) :
    firstQuadrantColumnPrefixToLastComponent K p q = 0 := by
  simp [firstQuadrantColumnPrefixToLastComponent, hq]

set_option backward.isDefEq.respectTransparency false in
/-- Projection of the finite prefix to its final outer column. -/
public noncomputable def firstQuadrantColumnPrefixToLast
    (K : FirstQuadrantBicomplex) (p : ℕ) :
    firstQuadrantColumnPrefix K p ⟶ firstQuadrantSingleColumn K p where
  f := firstQuadrantColumnPrefixToLastComponent K p
  comm' i j hij := by
    change j + 1 = i at hij
    by_cases hi : i = p
    · subst i
      have hj : j ≠ p := by
        omega
      rw [hi, firstQuadrantColumnPrefixToLastComponent_self,
        firstQuadrantColumnPrefixToLastComponent_eq_zero K p j hj,
        comp_zero]
      have hz : (firstQuadrantSingleColumn K p).d p j = 0 := by simp
      rw [hz, comp_zero]
    · rw [firstQuadrantColumnPrefixToLastComponent_eq_zero K p i hi,
        zero_comp]
      by_cases hj : j = p
      · subst j
        have hip : p < i := by
          omega
        have hz : IsZero ((firstQuadrantColumnPrefix K p).X i) :=
          firstQuadrantColumnPrefix_isZero_X K p i hip
        exact hz.eq_of_src _ _
      · rw [firstQuadrantColumnPrefixToLastComponent_eq_zero K p j hj,
          comp_zero]

noncomputable instance firstQuadrantColumnPrefixToLast_epi
    (K : FirstQuadrantBicomplex) (p : ℕ) :
    Epi (firstQuadrantColumnPrefixToLast K p) := by
  apply HomologicalComplex.epi_of_epi_f
  intro q
  by_cases hq : q = p
  · subst q
    dsimp [firstQuadrantColumnPrefixToLast]
    rw [firstQuadrantColumnPrefixToLastComponent_self]
    infer_instance
  · have hz : IsZero ((firstQuadrantSingleColumn K p).X q) :=
      HomologicalComplex.isZero_single_obj_X
        (ComplexShape.down ℕ) p (K.X p) q hq
    exact hz.epi _

end SphereSixComplex
