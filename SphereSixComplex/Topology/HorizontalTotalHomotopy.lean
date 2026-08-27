module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.TotalComplex

/-!
# Totalizing a horizontal chain homotopy of bicomplexes

A morphism of bicomplexes `K ⟶ M` (chain complexes of chain complexes) is a family of vertical
chain maps.  A chain homotopy between two such morphisms, taken in the outer chain-complex
category, has components `K.X p ⟶ M.X (p + 1)` which are themselves vertical chain maps.  This
file totalizes such a horizontal homotopy: on the summand in bidegree `(p, q)` the total homotopy
is the component into `(p + 1, q)`, with no sign because the horizontal sign `ε₁` of the total
complex shape is trivial.  The vertical cross terms cancel because the components are chain maps
and `ε₂ (p + 1, q) = -ε₂ (p, q)`.

This is the mirror image of `VerticallyNaturalHomotopy.totalHomotopy`; together they totalize
homotopies in either direction of a first-quadrant bicomplex.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace SphereSixComplex

section BicomplexLemmas

variable (K : HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ))

/-- A summand inclusion followed by the total differential is the sum of the horizontal and
vertical summand differentials. -/
@[reassoc]
public theorem ιTotal_total_d (p q n n' : ℕ)
    (hpq : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q) = n) :
    K.ιTotal (ComplexShape.down ℕ) p q n hpq ≫ (K.total (ComplexShape.down ℕ)).d n n' =
      K.d₁ (ComplexShape.down ℕ) p q n' + K.d₂ (ComplexShape.down ℕ) p q n' := by
  change _ ≫ (K.D₁ (ComplexShape.down ℕ) n n' + K.D₂ (ComplexShape.down ℕ) n n') = _
  rw [Preadditive.comp_add, HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂]

/-- The horizontal summand differential out of outer degree `p + 1`, with the trivial sign
`ε₁ = 1` removed. -/
public theorem d₁_succ (p q n : ℕ) :
    K.d₁ (ComplexShape.down ℕ) (p + 1) q n =
      (K.d (p + 1) p).f q ≫ K.ιTotalOrZero (ComplexShape.down ℕ) p q n := by
  rw [K.d₁_eq' (ComplexShape.down ℕ) (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl) q n]
  exact one_smul _ _

/-- The horizontal summand differential vanishes in outer degree zero. -/
public theorem d₁_zero (q n : ℕ) : K.d₁ (ComplexShape.down ℕ) 0 q n = 0 :=
  K.d₁_eq_zero (ComplexShape.down ℕ) 0 q n (by
    rw [ChainComplex.next_nat_zero]
    simp)

/-- The vertical summand differential out of inner degree `q + 1`. -/
public theorem d₂_succ (p q n : ℕ) :
    K.d₂ (ComplexShape.down ℕ) p (q + 1) n =
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p, q + 1) •
        ((K.X p).d (q + 1) q ≫ K.ιTotalOrZero (ComplexShape.down ℕ) p q n) :=
  K.d₂_eq' (ComplexShape.down ℕ) p (show (ComplexShape.down ℕ).Rel (q + 1) q from rfl) n

/-- The vertical summand differential vanishes in inner degree zero. -/
public theorem d₂_zero (p n : ℕ) : K.d₂ (ComplexShape.down ℕ) p 0 n = 0 :=
  K.d₂_eq_zero (ComplexShape.down ℕ) p 0 n (by
    rw [ChainComplex.next_nat_zero]
    simp)

end BicomplexLemmas

variable {K M : HomologicalComplex₂ AddCommGrpCat (ComplexShape.down ℕ) (ComplexShape.down ℕ)}
  {φ ψ : K ⟶ M} (h : Homotopy φ ψ)

/-- The summand formula for totalizing a horizontal homotopy: on bidegree `(p, q)` it is the
component `K.X p ⟶ M.X (p + 1)` in vertical degree `q`, followed by the inclusion of
`(p + 1, q)`, which is zero unless that bidegree has total degree `n'`. -/
public def horizontalTotalComponent (n n' : ℕ) :
    (K.total (ComplexShape.down ℕ)).X n ⟶ (M.total (ComplexShape.down ℕ)).X n' :=
  K.totalDesc fun p q _ ↦
    (h.hom p (p + 1)).f q ≫ M.ιTotalOrZero (ComplexShape.down ℕ) (p + 1) q n'

@[reassoc]
public theorem ιTotal_horizontalTotalComponent (p q n n' : ℕ)
    (hpq : ComplexShape.π (ComplexShape.down ℕ) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ) (p, q) = n) :
    K.ιTotal (ComplexShape.down ℕ) p q n hpq ≫ horizontalTotalComponent h n n' =
      (h.hom p (p + 1)).f q ≫ M.ιTotalOrZero (ComplexShape.down ℕ) (p + 1) q n' := by
  unfold horizontalTotalComponent
  rw [HomologicalComplex₂.ι_totalDesc]

/-- The summand formula in `ιTotalOrZero` form, for the slot `(n, n + 1)`. -/
@[reassoc]
public theorem ιTotalOrZero_horizontalTotalComponent (p q n : ℕ) :
    K.ιTotalOrZero (ComplexShape.down ℕ) p q n ≫ horizontalTotalComponent h n (n + 1) =
      (h.hom p (p + 1)).f q ≫ M.ιTotalOrZero (ComplexShape.down ℕ) (p + 1) q (n + 1) := by
  by_cases hpq : p + q = n
  · rw [K.ιTotalOrZero_eq (ComplexShape.down ℕ) p q n hpq, ιTotal_horizontalTotalComponent]
  · rw [K.ιTotalOrZero_eq_zero (ComplexShape.down ℕ) p q n hpq, zero_comp,
      M.ιTotalOrZero_eq_zero (ComplexShape.down ℕ) (p + 1) q (n + 1) (by
        change ¬ p + 1 + q = n + 1
        omega), comp_zero]

public theorem horizontalTotalComponent_zero (n n' : ℕ)
    (hn : ¬ (ComplexShape.down ℕ).Rel n' n) : horizontalTotalComponent h n n' = 0 := by
  apply HomologicalComplex₂.total.hom_ext
  intro p q hpq
  rw [ιTotal_horizontalTotalComponent, comp_zero, M.ιTotalOrZero_eq_zero, comp_zero]
  intro hpq'
  apply hn
  change p + q = n at hpq
  change p + 1 + q = n' at hpq'
  change n + 1 = n'
  omega

/-- The two vertical cross terms in the total homotopy equation cancel, because each component
of the horizontal homotopy is a vertical chain map and `ε₂` changes sign along the horizontal
differential. -/
public theorem vertical_terms_cancel (p q n : ℕ) :
    ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p, q + 1) •
        ((K.X p).d (q + 1) q ≫ (h.hom p (p + 1)).f q ≫
          M.ιTotalOrZero (ComplexShape.down ℕ) (p + 1) q n) +
      ComplexShape.ε₂ (ComplexShape.down ℕ) (ComplexShape.down ℕ) (ComplexShape.down ℕ)
          (p + 1, q + 1) •
        ((h.hom p (p + 1)).f (q + 1) ≫ (M.X (p + 1)).d (q + 1) q ≫
          M.ιTotalOrZero (ComplexShape.down ℕ) (p + 1) q n) = 0 := by
  rw [← Category.assoc ((h.hom p (p + 1)).f (q + 1)), (h.hom p (p + 1)).comm (q + 1) q,
    Category.assoc]
  change (ComplexShape.down ℕ).ε p • _ + (ComplexShape.down ℕ).ε (p + 1) • _ = 0
  rw [(ComplexShape.down ℕ).ε_succ (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl),
    Units.neg_smul, neg_add_cancel]

/-- The outer homotopy equation, in a fixed vertical degree. -/
public theorem hom_comm_f (p q : ℕ) :
    (φ.f p).f q =
      (dNext p h.hom).f q + (h.hom p (p + 1)).f q ≫ (M.d (p + 1) p).f q + (ψ.f p).f q := by
  have := congrArg (fun f ↦ HomologicalComplex.Hom.f f q) (h.comm p)
  rw [Homotopy.prevD_chainComplex] at this
  simpa only [HomologicalComplex.add_f_apply, HomologicalComplex.comp_f] using this

/-- A horizontal chain homotopy of bicomplex morphisms totalizes to a chain homotopy. -/
public def horizontalTotalHomotopy :
    Homotopy (HomologicalComplex₂.total.map φ (ComplexShape.down ℕ))
      (HomologicalComplex₂.total.map ψ (ComplexShape.down ℕ)) where
  hom := horizontalTotalComponent h
  zero := horizontalTotalComponent_zero h
  comm n := by
    apply HomologicalComplex₂.total.hom_ext
    intro p q hpq
    have hpq' : p + q = n := hpq
    rw [HomologicalComplex₂.ιTotal_map, Preadditive.comp_add, Preadditive.comp_add,
      HomologicalComplex₂.ιTotal_map]
    -- the `prevD` term
    have hprev : K.ιTotal (ComplexShape.down ℕ) p q n hpq ≫
          prevD n (horizontalTotalComponent h) =
        (h.hom p (p + 1)).f q ≫ (M.d (p + 1) p).f q ≫
            M.ιTotalOrZero (ComplexShape.down ℕ) p q n +
          ((h.hom p (p + 1)).f q ≫ M.d₂ (ComplexShape.down ℕ) (p + 1) q n :
            (K.X p).X q ⟶ (M.total (ComplexShape.down ℕ)).X n) := by
      rw [Homotopy.prevD_chainComplex, ← Category.assoc, ιTotal_horizontalTotalComponent,
        M.ιTotalOrZero_eq (ComplexShape.down ℕ) (p + 1) q (n + 1) (by
          change p + 1 + q = n + 1
          omega), Category.assoc, ιTotal_total_d, d₁_succ, Preadditive.comp_add]
    rw [hprev, ← M.ιTotalOrZero_eq (ComplexShape.down ℕ) p q n hpq]
    cases n with
    | zero =>
      obtain rfl : p = 0 := by omega
      obtain rfl : q = 0 := by omega
      rw [Homotopy.dNext_zero_chainComplex, comp_zero, zero_add, d₂_zero, comp_zero, add_zero,
        hom_comm_f h 0 0, Homotopy.dNext_zero_chainComplex, HomologicalComplex.zero_f_apply,
        zero_add, Preadditive.add_comp, Category.assoc]
    | succ m =>
      -- the `dNext` term
      have hnext : K.ιTotal (ComplexShape.down ℕ) p q (m + 1) hpq ≫
            dNext (m + 1) (horizontalTotalComponent h) =
          K.d₁ (ComplexShape.down ℕ) p q m ≫ horizontalTotalComponent h m (m + 1) +
            K.d₂ (ComplexShape.down ℕ) p q m ≫ horizontalTotalComponent h m (m + 1) := by
        rw [Homotopy.dNext_succ_chainComplex, ← Category.assoc, ιTotal_total_d,
          Preadditive.add_comp]
      rw [hnext]
      cases p with
      | zero =>
        rw [d₁_zero, zero_comp, zero_add, hom_comm_f h 0 q, Homotopy.dNext_zero_chainComplex,
          HomologicalComplex.zero_f_apply, zero_add, Preadditive.add_comp, Category.assoc]
        cases q with
        | zero => omega
        | succ q =>
          rw [d₂_succ, d₂_succ, Linear.units_smul_comp, Category.assoc,
            ιTotalOrZero_horizontalTotalComponent, Linear.comp_units_smul,
            ← Category.assoc ((h.hom 0 1).f (q + 1)), Category.assoc]
          have hv := vertical_terms_cancel h 0 q (m + 1)
          rw [eq_neg_of_add_eq_zero_left hv]
          abel
      | succ p =>
        rw [d₁_succ, Category.assoc, ιTotalOrZero_horizontalTotalComponent,
          hom_comm_f h (p + 1) q, Homotopy.dNext_succ_chainComplex,
          HomologicalComplex.comp_f, Preadditive.add_comp, Preadditive.add_comp,
          Category.assoc, Category.assoc]
        cases q with
        | zero =>
          rw [d₂_zero, zero_comp, add_zero, d₂_zero, comp_zero, add_zero]
        | succ q =>
          rw [d₂_succ, d₂_succ, Linear.units_smul_comp, Category.assoc,
            ιTotalOrZero_horizontalTotalComponent, Linear.comp_units_smul,
            ← Category.assoc ((h.hom (p + 1) (p + 1 + 1)).f (q + 1)), Category.assoc]
          have hv := vertical_terms_cancel h (p + 1) q (m + 1)
          have hv' := eq_neg_of_add_eq_zero_left hv
          rw [hv']
          abel

end SphereSixComplex
