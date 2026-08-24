module

public import SphereSixComplex.Geometry.Gluing

/-!
# Four-piece star gluings

The completed family is obtained by gluing three pairwise disjoint collars of the regular piece
to collars in the cusp and two elliptic fillings.  This file turns exactly that data into
`TopCat.GlueData`.
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace SphereSixComplex

/-- Three fillings attached along pairwise disjoint open collars of one central piece. -/
public structure FourPieceStarGluingData where
  central : TopCat
  filling : Fin 3 → TopCat
  centralCollar : Fin 3 → Opens central
  fillingCollar : ∀ i, Opens (filling i)
  collarEquiv : ∀ i, centralCollar i ≃ₜ fillingCollar i
  centralCollar_disjoint : Pairwise fun i j ↦ Disjoint (centralCollar i) (centralCollar j)

namespace FourPieceStarGluingData

variable (A : FourPieceStarGluingData)

/-- The central piece is indexed by `none`; the three fillings are indexed by `some i`. -/
public def piece : Option (Fin 3) → TopCat
  | none => A.central
  | some i => A.filling i

/-- Pairwise overlaps in the star diagram.  Distinct fillings do not overlap directly. -/
public def overlap : ∀ i, Option (Fin 3) → Opens (A.piece i)
  | none, none => ⊤
  | none, some j => A.centralCollar j
  | some i, none => A.fillingCollar i
  | some i, some j => if i = j then ⊤ else ⊥

public noncomputable def transition : ∀ i j,
    (Opens.toTopCat _).obj (A.overlap i j) ⟶
      (Opens.toTopCat _).obj (A.overlap j i)
  | none, none => 𝟙 _
  | none, some j => TopCat.ofHom ⟨A.collarEquiv j, (A.collarEquiv j).continuous⟩
  | some i, none => TopCat.ofHom ⟨(A.collarEquiv i).symm,
      (A.collarEquiv i).symm.continuous⟩
  | some i, some j => by
      by_cases h : i = j
      · subst j
        exact 𝟙 _
      · haveI : IsEmpty (A.overlap (some i) (some j)) := by
          constructor
          intro x
          simpa [overlap, h] using x.2
        haveI : IsEmpty (A.overlap (some j) (some i)) := by
          constructor
          intro x
          simpa [overlap, Ne.symm h] using x.2
        exact TopCat.ofHom ⟨Homeomorph.empty, Homeomorph.empty.continuous⟩

@[simp]
public theorem transition_none_none_apply (x : A.overlap none none) :
    A.transition none none x = x :=
  rfl

@[simp]
public theorem transition_none_some_apply (j : Fin 3) (x : A.overlap none (some j)) :
    A.transition none (some j) x = A.collarEquiv j x :=
  rfl

@[simp]
public theorem transition_some_none_apply (i : Fin 3) (x : A.overlap (some i) none) :
    A.transition (some i) none x = (A.collarEquiv i).symm x :=
  rfl

@[simp]
public theorem transition_some_self_apply (i : Fin 3) (x : A.overlap (some i) (some i)) :
    A.transition (some i) (some i) x = x := by
  simp [transition, Function.id_def]
  rfl

@[simp]
public theorem transition_none_none_val (x : A.overlap none none) :
    (A.transition none none x).1 = x.1 :=
  congrArg Subtype.val (A.transition_none_none_apply x)

@[simp]
public theorem transition_none_some_val (j : Fin 3) (x : A.overlap none (some j)) :
    (A.transition none (some j) x).1 = (A.collarEquiv j x).1 :=
  congrArg Subtype.val (A.transition_none_some_apply j x)

@[simp]
public theorem transition_some_none_val (i : Fin 3) (x : A.overlap (some i) none) :
    (A.transition (some i) none x).1 = ((A.collarEquiv i).symm x).1 :=
  congrArg Subtype.val (A.transition_some_none_apply i x)

@[simp]
public theorem transition_some_self_val (i : Fin 3)
    (x : A.overlap (some i) (some i)) :
    (A.transition (some i) (some i) x).1 = x.1 :=
  congrArg Subtype.val (A.transition_some_self_apply i x)

public theorem overlap_id (i : Option (Fin 3)) : A.overlap i i = ⊤ := by
  cases i with
  | none => rfl
  | some i => simp [overlap]

public theorem transition_id (i : Option (Fin 3)) : ⇑(A.transition i i) = id := by
  cases i with
  | none => rfl
  | some i => simp [transition]

public theorem transition_inter
    {i j : Option (Fin 3)} (k : Option (Fin 3)) (x : A.overlap i j) (hx : ↑x ∈ A.overlap i k) :
    (((↑) : (A.overlap j i) → (A.piece j))
      (A.transition i j x)) ∈ A.overlap j k := by
  cases i with
  | none =>
      cases j with
      | none =>
          rw [transition_none_none_val]
          exact hx
      | some j =>
          cases k with
          | none =>
              change (A.transition none (some j) x).1 ∈ A.fillingCollar j
              rw [transition_none_some_val]
              exact (A.collarEquiv j x).2
          | some k =>
              by_cases hjk : j = k
              · subst k
                simp [overlap]
              · exfalso
                have hmem : x.1 ∈ A.centralCollar j ⊓ A.centralCollar k := ⟨x.2, hx⟩
                rw [(A.centralCollar_disjoint hjk).eq_bot] at hmem
                change False at hmem
                exact hmem
  | some i =>
      cases j with
      | none =>
          cases k with
          | none =>
              simp [overlap]
          | some k =>
              by_cases hik : i = k
              · subst k
                change (A.transition (some i) none x).1 ∈ A.centralCollar i
                rw [transition_some_none_val]
                exact ((A.collarEquiv i).symm x).2
              · exfalso
                simp [overlap, hik] at hx
      | some j =>
          by_cases hij : i = j
          · subst j
            cases k with
            | none =>
                change (A.transition (some i) (some i) x).1 ∈ A.fillingCollar i
                rw [transition_some_self_val]
                exact hx
            | some k =>
                change (A.transition (some i) (some i) x).1 ∈
                  (if i = k then ⊤ else ⊥)
                rw [transition_some_self_val]
                exact hx
          · exfalso
            simpa [overlap, hij] using x.2

public theorem transition_cocycle
    (i j k : Option (Fin 3)) (x : A.overlap i j) (hx : ↑x ∈ A.overlap i k) :
    (((↑) : (A.overlap k j) → (A.piece k))
        (A.transition j k ⟨_, A.transition_inter k x hx⟩)) =
      ((↑) : (A.overlap k i) → (A.piece k))
        (A.transition i k ⟨x, hx⟩) := by
  cases i <;> cases j <;> cases k <;> simp_all [overlap, transition] <;>
    try rfl
  case none.some.none j =>
    change ((A.collarEquiv j).symm (A.collarEquiv j x)).1 = x.1
    exact congrArg Subtype.val ((A.collarEquiv j).symm_apply_apply x)
  case none.some.some j k =>
    by_cases h : j = k
    · subst k
      simp
      rfl
    · exfalso
      have hmem : x.1 ∈ A.centralCollar j ⊓ A.centralCollar k := ⟨x.2, hx⟩
      rw [(A.centralCollar_disjoint h).eq_bot] at hmem
      change False at hmem
      exact hmem
  case some.none.some i k =>
    by_cases h : i = k
    · subst k
      simp
      change (A.collarEquiv i ((A.collarEquiv i).symm x)).1 = x.1
      exact congrArg Subtype.val ((A.collarEquiv i).apply_symm_apply x)
    · exfalso
      simp [overlap, h] at hx
  case some.some.none i j =>
    by_cases h : i = j
    · subst j
      simp
      rfl
    · exfalso
      simpa [overlap, h] using x.2
  case some.some.some i j k =>
    by_cases hij : i = j
    · subst j
      by_cases hik : i = k
      · subst k
        simp
        rfl
      · exfalso
        simp [overlap, hik] at hx
    · exfalso
      simpa [overlap, hij] using x.2

/-- The canonical four-piece topological gluing diagram associated to a star of collars. -/
public noncomputable def glueData : TopCat.GlueData :=
  TopCat.GlueData.mk' {
    J := Option (Fin 3)
    U := A.piece
    V := A.overlap
    t := transition A
    V_id := overlap_id A
    t_id := transition_id A
    t_inter := fun _ _ k x hx ↦ transition_inter A k x hx
    cocycle := transition_cocycle A }

end FourPieceStarGluingData

end SphereSixComplex
